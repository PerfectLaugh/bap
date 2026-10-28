#![forbid(unsafe_code)]

mod bil;
mod eval;
mod types;
pub mod wire;

pub use bil::{fold_bil, fold_exp, propagate_consts, prune_dead_virtuals};
pub use eval::{Error, Evaluator, Memory, Result, Value};
pub use types::{
    Arg, Bil, BinOp, Blk, Cast, Def, Endian, Exp, Jmp, JmpKind, Label, Phi, Program, Stmt, Sub,
    Tid, Type, UnOp, Var,
};

#[cfg(test)]
mod tests {
    use super::*;

    fn var(name: &str) -> Var {
        Var::new(name, Type::Int(8))
    }

    #[test]
    fn evaluates_expressions_and_memory() {
        for endian in [Endian::Little, Endian::Big] {
            let memory = Var::new(
                "mem",
                Type::Mem {
                    address: 64,
                    value: 8,
                },
            );
            let mut evaluator = Evaluator::new(64);
            evaluator.bind(memory.clone(), Value::Memory(Memory::new(64)));
            let address = Exp::int(bap_bitvec::BitVec::from_u64(64, 0x1000));
            let value = Exp::int(bap_bitvec::BitVec::from_u64(16, 0xabcd));
            let store = Exp::store(Exp::Var(memory.clone()), address.clone(), value, endian, 2);
            let stored = evaluator.eval(&store).unwrap();
            assert!(matches!(stored, Value::Memory(_)));
            evaluator
                .eval_def(&Def {
                    tid: 1,
                    var: memory.clone(),
                    rhs: store,
                })
                .unwrap();
            let load = Exp::load(Exp::Var(memory), address, endian, 2);
            assert_eq!(
                evaluator.eval(&load).unwrap().bits().unwrap().to_u64(),
                Some(0xabcd)
            );
        }
        let mut evaluator = Evaluator::new(64);
        let arithmetic = Exp::bin(
            BinOp::Add,
            Exp::int(bap_bitvec::BitVec::from_u64(4, 15)),
            Exp::int(bap_bitvec::BitVec::from_u64(4, 1)),
        );
        assert_eq!(
            evaluator
                .eval(&arithmetic)
                .unwrap()
                .bits()
                .unwrap()
                .to_u64(),
            Some(0)
        );
    }

    #[test]
    fn conditionals_casts_and_errors() {
        let mut evaluator = Evaluator::new(64);
        let expression = Exp::ite(
            Exp::int(bap_bitvec::BitVec::one(1)),
            Exp::cast(
                Cast::Signed,
                16,
                Exp::int(bap_bitvec::BitVec::from_u64(8, 0x80)),
            ),
            Exp::int(bap_bitvec::BitVec::zero(16)),
        );
        assert_eq!(
            evaluator
                .eval(&expression)
                .unwrap()
                .bits()
                .unwrap()
                .to_u64(),
            Some(0xff80)
        );
        assert!(
            evaluator
                .eval(&Exp::Unknown("undefined".into(), Type::Int(8)))
                .is_err()
        );
        assert!(evaluator.eval(&Exp::var(var("missing"))).is_err());
    }

    #[test]
    fn substitution_and_free_variables_respect_let_bindings() {
        let x = var("x");
        let expression = Exp::Let {
            var: x.clone(),
            value: Box::new(Exp::Var(x.clone())),
            body: Box::new(Exp::Var(x.clone())),
        };
        assert_eq!(
            expression.free_vars(),
            std::collections::BTreeSet::from([x.clone()])
        );
        let replacement = Exp::int(bap_bitvec::BitVec::from_u64(8, 42));
        let substituted = expression.substitute(&std::collections::BTreeMap::from([(
            x,
            replacement.clone(),
        )]));
        assert_eq!(
            substituted,
            Exp::Let {
                var: var("x"),
                value: Box::new(replacement),
                body: Box::new(Exp::Var(var("x"))),
            }
        );
    }

    #[test]
    fn bir_serde_round_trip() {
        let program = Program::new(vec![Sub::new(1, "main")]);
        let json = serde_json::to_string(&program).unwrap();
        assert_eq!(serde_json::from_str::<Program>(&json).unwrap(), program);
    }
}
