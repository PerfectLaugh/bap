use crate::model::{WStmt, stmts_from_wire, stmts_to_wire};
use std::collections::LinkedList;

#[ocaml::func]
pub fn bap_bir_rs_fold_consts(input: LinkedList<WStmt>) -> Result<LinkedList<WStmt>, String> {
    Ok(stmts_to_wire(&bap_bir::fold_bil(&stmts_from_wire(&input))))
}

#[ocaml::func]
pub fn bap_bir_rs_propagate_consts(input: LinkedList<WStmt>) -> Result<LinkedList<WStmt>, String> {
    Ok(stmts_to_wire(&bap_bir::propagate_consts(&stmts_from_wire(
        &input,
    ))))
}

#[ocaml::func]
pub fn bap_bir_rs_prune_dead_virtuals(
    input: LinkedList<WStmt>,
) -> Result<LinkedList<WStmt>, String> {
    Ok(stmts_to_wire(&bap_bir::prune_dead_virtuals(
        &stmts_from_wire(&input),
    )))
}
