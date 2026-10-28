#![deny(unsafe_op_in_unsafe_fn)]

use bap_knowledge::{FullName, Object, Order, Pid, Runtime, Slot, State};
use ocaml::{FromValue, Pointer, Runtime as OcamlRuntime, Value};
use std::cell::RefCell;
use std::collections::LinkedList;
use std::rc::Rc;

type NativeValue = Rc<Value>;

fn rt() -> &'static OcamlRuntime {
    // SAFETY: ocaml-rs owns the process runtime and roots values used by this crate.
    unsafe { OcamlRuntime::recover_handle() }
}
fn field(value: &Value, index: usize) -> Value {
    // SAFETY: the OCaml records are created by the matching wrappers and have these fields.
    unsafe { value.field(index) }
}
fn named(name: &str) -> Value {
    // SAFETY: bap_knowledge.ml registers these exact names at library initialization.
    unsafe { Value::named(name).unwrap_or_else(|| panic!("missing OCaml helper {name}")) }
}
fn call1(function: &str, left: &Value) -> Result<Value, String> {
    // SAFETY: registered helpers are closures with the declared arity and matching value layouts.
    unsafe {
        named(function)
            .call::<1, Value>(rt(), [left.clone()])
            .map_err(|error| format!("{error:?}"))
    }
}
fn call2(function: &str, left: &Value, right: &Value) -> Result<Value, String> {
    // SAFETY: registered helpers are closures with the declared arity and matching value layouts.
    unsafe {
        named(function)
            .call::<2, Value>(rt(), [left.clone(), right.clone()])
            .map_err(|error| format!("{error:?}"))
    }
}
fn call3(function: &str, first: &Value, second: &Value, third: &Value) -> Result<Value, String> {
    // SAFETY: registered helpers are closures with the declared arity and matching value layouts.
    unsafe {
        named(function)
            .call::<3, Value>(rt(), [first.clone(), second.clone(), third.clone()])
            .map_err(|error| format!("{error:?}"))
    }
}
fn call4(
    function: &str,
    first: &Value,
    second: &Value,
    third: &Value,
    fourth: &Value,
) -> Result<Value, String> {
    // SAFETY: registered helpers are closures with the declared arity and matching value layouts.
    unsafe {
        named(function)
            .call::<4, Value>(
                rt(),
                [first.clone(), second.clone(), third.clone(), fourth.clone()],
            )
            .map_err(|error| format!("{error:?}"))
    }
}
fn ok(value: Value) -> Result<Value, String> {
    // SAFETY: Result is a one-field block with tag 0 for Ok and tag 1 for Error.
    unsafe {
        if value.tag() == ocaml::Tag(0) {
            Ok(field(&value, 0))
        } else {
            Err(format!("{:?}", field(&value, 0)))
        }
    }
}
fn int(value: isize) -> Value {
    // SAFETY: isize is the OCaml int representation used by the interop types.
    unsafe { Value::int(value) }
}
fn int_value(value: &Value) -> isize {
    // SAFETY: integer results returned by the OCaml helpers are plain OCaml ints.
    unsafe { value.int_val() }
}
fn uint(value: u64) -> Value {
    int(value as isize)
}
fn rooted(value: Value) -> NativeValue {
    Rc::new(value.root())
}
fn unrooted(value: &NativeValue) -> Value {
    value.as_ref().clone()
}
#[derive(Clone)]
struct NativeRuntime {
    slot: Value,
    env: RefCell<Value>,
}
impl NativeRuntime {
    fn new(slot: Value) -> Self {
        Self::with_env(slot, Value::unit())
    }
    fn with_env(slot: Value, env: Value) -> Self {
        Self {
            slot: slot.root(),
            env: RefCell::new(env.root()),
        }
    }
    fn env(&self) -> Value {
        self.env.borrow().clone()
    }
    fn finish_env(&self, state: &State<NativeValue>) -> Result<Value, String> {
        call2("kb_native_with_env", &self.env(), &state_to_value(state))
    }
    fn get(&self, data: &Value) -> Result<Value, String> {
        call2("kb_native_get", &self.slot, data)
    }
    fn empty_record(&self) -> NativeValue {
        rooted(named("kb_native_empty_record"))
    }
}
impl Runtime<NativeValue> for NativeRuntime {
    fn empty_record(&self) -> NativeValue {
        NativeRuntime::empty_record(self)
    }
    fn current(&self, state: &State<NativeValue>, slot: &Slot, object: Object) -> NativeValue {
        let data = class_value(state, slot)
            .and_then(|class| class.vals.get(&object))
            .map_or_else(|| self.empty_record(), |info| info.data.clone());
        rooted(self.get(&data).expect("record get"))
    }
    fn slot_is_empty(&self, _slot: &Slot, value: &NativeValue) -> bool {
        int_value(&call2("kb_native_is_empty", &self.slot, value).expect("domain empty check")) != 0
    }
    fn order(&self, _slot: &Slot, left: &NativeValue, right: &NativeValue) -> Order {
        match int_value(&call3("kb_native_order", &self.slot, left, right).expect("domain order")) {
            0 => Order::Less,
            1 => Order::Equal,
            2 => Order::Greater,
            _ => Order::Incomparable,
        }
    }
    fn initial_promises(&self, _slot: &Slot) -> Vec<Pid> {
        let values: LinkedList<isize> = ocaml::FromValue::from_value(
            call1("kb_native_promises", &self.slot).expect("promise ids"),
        );
        values.iter().map(|value| *value as u64).collect()
    }
    fn run(
        &self,
        state: State<NativeValue>,
        _slot: &Slot,
        object: Object,
        pid: Pid,
    ) -> Result<State<NativeValue>, String> {
        let handle = state_to_value(&state);
        let env = call2("kb_native_with_env", &self.env(), &handle)?;
        let state = ok(call4(
            "kb_native_run",
            &self.slot,
            &int(pid as isize),
            &uint(object),
            &env,
        )?)?;
        let native = field(&state, 3);
        let rust = value_to_state(native);
        self.env.replace(state);
        Ok(rust)
    }
    fn commit(
        &self,
        _state: &State<NativeValue>,
        _slot: &Slot,
        old: Option<&NativeValue>,
        value: &NativeValue,
    ) -> Result<NativeValue, String> {
        let old = old.map_or_else(|| self.empty_record(), Clone::clone);
        Ok(rooted(ok(call3(
            "kb_native_commit",
            &self.slot,
            &old,
            value,
        )?)?))
    }
}

fn class_value<'a>(
    state: &'a State<NativeValue>,
    name: &bap_knowledge::Name,
) -> Option<&'a bap_knowledge::ClassState<NativeValue>> {
    state.classes.get(name)
}
struct NativeState(State<NativeValue>);

impl ocaml::Custom for NativeState {
    const NAME: &'static str = "bap.knowledge.NativeState\0";
    const OPS: ocaml::custom::CustomOps = ocaml::custom::CustomOps {
        identifier: Self::NAME.as_ptr() as *const ocaml::sys::Char,
        finalize: Some(Self::finalize),
        ..ocaml::custom::DEFAULT_CUSTOM_OPS
    };
}

fn state_to_value(state: &State<NativeValue>) -> Value {
    Pointer::alloc_custom(NativeState(state.clone())).0
}
fn value_to_state(value: Value) -> State<NativeValue> {
    Pointer::<NativeState>::from_value(value).as_ref().0.clone()
}

#[ocaml::func]
pub fn kb_rs_empty() -> Value {
    static INIT: std::sync::Once = std::sync::Once::new();
    INIT.call_once(|| {
        // SAFETY: called from OCaml while holding the domain lock, before creating roots.
        assert!(unsafe { ocaml_boxroot_sys::boxroot_setup() });
    });
    state_to_value(&State::default())
}
#[ocaml::func]
pub fn kb_rs_create(state: Value, name: &str) -> Result<(Value, Value), String> {
    let state = value_to_state(state);
    let (state, object) = bap_knowledge::create(state, &name.to_string());
    Ok((state_to_value(&state), uint(object)))
}
#[ocaml::func]
pub fn kb_rs_delete(state: Value, name: &str, object: isize) -> Value {
    state_to_value(&bap_knowledge::delete(
        value_to_state(state),
        &name.to_string(),
        object as u64,
    ))
}
#[ocaml::func]
pub fn kb_rs_objects(state: Value, name: &str) -> Vec<isize> {
    bap_knowledge::objects(&value_to_state(state), &name.to_string())
        .into_iter()
        .map(|object| object as isize)
        .collect()
}
#[ocaml::func]
pub fn kb_rs_intern(
    state: Value,
    name: &str,
    package: &str,
    symbol: &str,
    public: bool,
) -> Result<(Value, Value), String> {
    let state = value_to_state(state);
    let empty = NativeRuntime::new(Value::unit()).empty_record();
    let (state, object) = bap_knowledge::intern(
        state,
        &name.to_string(),
        FullName::new(package, symbol),
        public,
        &empty,
    );
    Ok((state_to_value(&state), uint(object)))
}
#[ocaml::func]
pub fn kb_rs_repr(state: Value, name: &str, object: isize) -> String {
    bap_knowledge::repr(&value_to_state(state), &name.to_string(), object as u64)
}
#[ocaml::func]
pub fn kb_rs_read(state: Value, name: &str, input: &str) -> Result<(Value, Value), String> {
    let state = value_to_state(state);
    let empty = NativeRuntime::new(Value::unit()).empty_record();
    let (state, object) = bap_knowledge::read(state, &name.to_string(), input, &empty);
    Ok((state_to_value(&state), uint(object)))
}
#[ocaml::func]
pub fn kb_rs_current(state: Value, slot: Value, object: isize) -> Value {
    let runtime = NativeRuntime::new(slot);
    let slot_name = runtime.slot_name();
    unrooted(&bap_knowledge::current(
        &value_to_state(state),
        &runtime,
        &slot_name,
        object as u64,
    ))
}
#[ocaml::func]
pub fn kb_rs_record(state: Value, name: &str, object: isize) -> Value {
    let state = value_to_state(state);
    let empty = NativeRuntime::new(Value::unit()).empty_record();
    unrooted(
        &class_value(&state, &name.to_string())
            .and_then(|class| class.vals.get(&(object as u64)))
            .map_or(empty, |info| info.data.clone()),
    )
}

#[ocaml::func]
pub fn kb_rs_provide(
    state: Value,
    slot: Value,
    object: isize,
    value: Value,
) -> Result<Value, String> {
    let runtime = NativeRuntime::with_env(slot, state.clone());
    let name = runtime.slot_name();
    let native = field(&state, 3);
    let state = bap_knowledge::provide(
        value_to_state(native),
        &runtime,
        &name,
        object as u64,
        &rooted(value),
    )?;
    runtime.finish_env(&state)
}
#[ocaml::func]
pub fn kb_rs_status(state: Value, slot: Value, object: isize) -> (isize, Value) {
    let runtime = NativeRuntime::new(slot);
    let name = runtime.slot_name();
    let state = value_to_state(state);
    match bap_knowledge::status(&state, &runtime, &name, object as u64) {
        bap_knowledge::Status::Sleep => (0, unrooted(&runtime.empty_record())),
        bap_knowledge::Status::Awoke => (1, unrooted(&runtime.empty_record())),
        bap_knowledge::Status::Ready(data) => (2, unrooted(&data)),
    }
}

#[ocaml::func]
pub fn kb_rs_collect(state: Value, slot: Value, object: isize) -> Result<(Value, Value), String> {
    let runtime = NativeRuntime::with_env(slot, state.clone());
    let name = runtime.slot_name();
    let native = field(&state, 3);
    let (state, value) =
        bap_knowledge::collect(value_to_state(native), &runtime, &name, object as u64)?;
    Ok((runtime.finish_env(&state)?, unrooted(&value)))
}
#[ocaml::func]
pub fn kb_rs_set_package(state: Value, package: &str) -> Value {
    state_to_value(&bap_knowledge::set_package(value_to_state(state), package))
}
#[ocaml::func]
pub fn kb_rs_import(
    state: Value,
    imports: LinkedList<String>,
    strict: bool,
) -> Result<Value, String> {
    let imports = imports.into_iter().collect::<Vec<_>>();
    bap_knowledge::import(value_to_state(state), &imports, strict)
        .map(|state| state_to_value(&state))
}

impl NativeRuntime {
    fn slot_name(&self) -> Slot {
        let class = call1("kb_native_class", &self.slot).expect("class name");
        let name = call1("kb_native_slot_name", &self.slot).expect("slot name");
        Slot::new(String::from_value(class), String::from_value(name))
    }
}
