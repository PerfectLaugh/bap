#![forbid(unsafe_code)]

use imbl::{OrdMap, OrdSet};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::atomic::{AtomicU64, Ordering};

pub type Name = String;
pub type Object = u64;
pub type Pid = u64;

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct Slot {
    pub class: Name,
    pub name: Name,
}

impl Slot {
    pub fn new(class: impl Into<Name>, name: impl Into<Name>) -> Self {
        Self {
            class: class.into(),
            name: name.into(),
        }
    }
}

impl std::ops::Deref for Slot {
    type Target = Name;

    fn deref(&self) -> &Self::Target {
        &self.class
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Order {
    Less,
    Equal,
    Greater,
    Incomparable,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct FullName {
    pub package: String,
    pub name: String,
}
impl FullName {
    pub fn new(package: impl Into<String>, name: impl Into<String>) -> Self {
        Self {
            package: package.into(),
            name: name.into(),
        }
    }
    pub fn show(&self) -> String {
        if self.package == "user" || self.package == "keyword" {
            self.name.clone()
        } else {
            format!("{}:{}", self.package, self.name)
        }
    }
}

#[derive(Clone, Debug)]
pub enum Work {
    Done,
    Work {
        waiting: BTreeSet<Pid>,
        current: BTreeSet<Pid>,
    },
}
impl Work {
    fn empty() -> Self {
        Self::Work {
            waiting: BTreeSet::new(),
            current: BTreeSet::new(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct ObjectInfo<V> {
    pub data: V,
    pub comp: BTreeMap<Slot, Work>,
    pub name: Option<FullName>,
}

#[derive(Clone, Debug)]
pub struct ClassState<V> {
    pub last: Object,
    pub vals: OrdMap<Object, ObjectInfo<V>>,
    pub objs: OrdMap<FullName, Object>,
    pub pubs: OrdMap<String, OrdSet<Object>>,
}
impl<V> Default for ClassState<V> {
    fn default() -> Self {
        Self {
            last: 1,
            vals: OrdMap::new(),
            objs: OrdMap::new(),
            pubs: OrdMap::new(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct State<V> {
    pub classes: OrdMap<Name, ClassState<V>>,
    pub package: String,
}
impl<V> Default for State<V> {
    fn default() -> Self {
        Self {
            classes: OrdMap::new(),
            package: "user".into(),
        }
    }
}

#[derive(Debug)]
pub enum Status<V> {
    Sleep,
    Awoke,
    Ready(V),
}

pub trait Runtime<V> {
    fn empty_record(&self) -> V;
    fn current(&self, state: &State<V>, slot: &Slot, object: Object) -> V;
    fn slot_is_empty(&self, slot: &Slot, value: &V) -> bool;
    fn order(&self, slot: &Slot, left: &V, right: &V) -> Order;
    fn initial_promises(&self, slot: &Slot) -> Vec<Pid>;
    fn run(
        &self,
        state: State<V>,
        slot: &Slot,
        object: Object,
        pid: Pid,
    ) -> Result<State<V>, String>;
    fn commit(
        &self,
        state: &State<V>,
        slot: &Slot,
        old: Option<&V>,
        value: &V,
    ) -> Result<V, String>;
}

fn class<V: Clone>(state: &State<V>, name: &Name) -> ClassState<V> {
    state.classes.get(name).cloned().unwrap_or_default()
}
fn put_class<V: Clone>(state: &mut State<V>, name: &Name, objects: ClassState<V>) {
    state.classes.insert(name.clone(), objects);
}
fn with_objects<V: Clone>(
    state: &mut State<V>,
    name: &Name,
    update: impl FnOnce(&mut ClassState<V>),
) {
    let mut objects = class(state, name);
    update(&mut objects);
    put_class(state, name, objects);
}

static LAST_OBJECT: AtomicU64 = AtomicU64::new(0);
fn fresh<V>(objects: &mut ClassState<V>) -> Object {
    let next = objects.last.max(LAST_OBJECT.load(Ordering::Relaxed)) + 1;
    LAST_OBJECT.store(next, Ordering::Relaxed);
    objects.last = next;
    next
}

pub fn create<V: Clone>(mut state: State<V>, name: &Name) -> (State<V>, Object) {
    let mut objects = class(&state, name);
    let object = fresh(&mut objects);
    put_class(&mut state, name, objects);
    (state, object)
}

pub fn delete<V: Clone>(mut state: State<V>, name: &Name, object: Object) -> State<V> {
    with_objects(&mut state, name, |objects| {
        objects.vals.remove(&object);
    });
    state
}

pub fn objects<V: Clone>(state: &State<V>, name: &Name) -> Vec<Object> {
    class(state, name).vals.keys().copied().collect()
}

pub fn intern<V: Clone>(
    mut state: State<V>,
    name: &Name,
    symbol: FullName,
    public: bool,
    empty_record: &V,
) -> (State<V>, Object) {
    let mut objects = class(&state, name);
    let object = match objects.objs.get(&symbol).copied() {
        Some(object) => object,
        None => {
            let object = fresh(&mut objects);
            objects.objs.insert(symbol.clone(), object);
            object
        }
    };
    objects
        .vals
        .entry(object)
        .and_modify(|info| info.name = Some(symbol.clone()))
        .or_insert_with(|| ObjectInfo {
            data: empty_record.clone(),
            comp: BTreeMap::new(),
            name: Some(symbol.clone()),
        });
    if public {
        objects
            .pubs
            .entry(symbol.package.clone())
            .or_default()
            .insert(object);
    }
    put_class(&mut state, name, objects);
    (state, object)
}

pub fn repr<V: Clone>(state: &State<V>, name: &Name, object: Object) -> String {
    if object == 0 {
        return "nil".into();
    }
    let objects = class(state, name);
    let Some(info) = objects.vals.get(&object) else {
        return format!("#<{} {object:#x}>", name);
    };
    match &info.name {
        Some(symbol) if symbol.package == state.package => symbol.name.clone(),
        Some(symbol) => symbol.show(),
        _ => format!("#<{} {object:#x}>", name),
    }
}

pub fn read<V: Clone>(
    state: State<V>,
    name: &Name,
    input: &str,
    empty_record: &V,
) -> (State<V>, Object) {
    if input == "nil" {
        return (state, 0);
    }
    if let Some(hex) = input.strip_prefix("#<")
        && let Some((_, address)) = hex.rsplit_once(' ')
        && let Ok(object) =
            u64::from_str_radix(address.trim_end_matches('>').trim_start_matches("0x"), 16)
    {
        return (state, object);
    }
    let (package, symbol) = input
        .split_once(':')
        .map_or((state.package.clone(), input.to_string()), |(p, s)| {
            (p.to_string(), s.to_string())
        });
    intern(
        state,
        name,
        FullName::new(package, symbol),
        false,
        empty_record,
    )
}

pub fn current<V>(state: &State<V>, runtime: &impl Runtime<V>, slot: &Slot, object: Object) -> V {
    runtime.current(state, slot, object)
}

pub fn provide<V: Clone>(
    mut state: State<V>,
    runtime: &impl Runtime<V>,
    slot: &Slot,
    object: Object,
    value: &V,
) -> Result<State<V>, String> {
    if object == 0 || runtime.slot_is_empty(slot, value) {
        return Ok(state);
    }
    let old = class(&state, slot).vals.get(&object).cloned();
    let data = runtime.commit(&state, slot, old.as_ref().map(|info| &info.data), value)?;
    let info = match old {
        Some(old) => ObjectInfo { data, ..old },
        None => ObjectInfo {
            data,
            comp: BTreeMap::new(),
            name: None,
        },
    };
    with_objects(&mut state, &slot.clone(), |objects| {
        objects.vals.insert(object, info);
    });
    Ok(state)
}

fn update_slot_with<V: Clone>(
    state: &mut State<V>,
    runtime: &impl Runtime<V>,
    slot: &Slot,
    object: Object,
    update: impl FnOnce(Option<Work>) -> Work,
) {
    let name = slot.clone();
    with_objects(state, &name, |objects| {
        let info = objects.vals.entry(object).or_insert_with(|| ObjectInfo {
            data: runtime.empty_record(),
            comp: BTreeMap::new(),
            name: None,
        });
        let work = info.comp.remove(slot);
        info.comp.insert(slot.clone(), update(work));
    });
}

fn enter_slot<V: Clone>(
    state: &mut State<V>,
    runtime: &impl Runtime<V>,
    slot: &Slot,
    object: Object,
) {
    update_slot_with(state, runtime, slot, object, |work| {
        assert!(work.is_none(), "slot entered twice");
        Work::empty()
    });
}
fn leave_slot<V: Clone>(
    state: &mut State<V>,
    runtime: &impl Runtime<V>,
    slot: &Slot,
    object: Object,
) {
    update_slot_with(state, runtime, slot, object, |work| {
        assert!(
            matches!(work, Some(Work::Work { .. })),
            "slot left without entry"
        );
        Work::Done
    });
}
fn enter_promise<V: Clone>(
    state: &mut State<V>,
    runtime: &impl Runtime<V>,
    slot: &Slot,
    object: Object,
    pid: Pid,
) {
    update_slot_with(state, runtime, slot, object, |work| {
        let Some(Work::Work {
            waiting,
            mut current,
        }) = work
        else {
            panic!("promise entered outside of work")
        };
        current.insert(pid);
        Work::Work { waiting, current }
    });
}
fn leave_promise<V: Clone>(
    state: &mut State<V>,
    runtime: &impl Runtime<V>,
    slot: &Slot,
    object: Object,
    pid: Pid,
) {
    update_slot_with(state, runtime, slot, object, |work| {
        let Some(Work::Work {
            waiting,
            mut current,
        }) = work
        else {
            panic!("promise left outside of work")
        };
        current.remove(&pid);
        Work::Work { waiting, current }
    });
}
fn enqueue_promises<V: Clone>(
    state: &mut State<V>,
    runtime: &impl Runtime<V>,
    slot: &Slot,
    object: Object,
) {
    update_slot_with(state, runtime, slot, object, |work| {
        let Some(Work::Work {
            mut waiting,
            current,
        }) = work
        else {
            panic!("enqueue outside of work")
        };
        waiting.extend(current);
        Work::Work {
            waiting,
            current: BTreeSet::new(),
        }
    });
}
fn dequeue_waiting<V: Clone>(
    state: &mut State<V>,
    runtime: &impl Runtime<V>,
    slot: &Slot,
    object: Object,
) -> Vec<Pid> {
    let mut result = Vec::new();
    update_slot_with(state, runtime, slot, object, |work| {
        let Some(Work::Work { waiting, current }) = work else {
            panic!("dequeue outside of work")
        };
        result.extend(waiting);
        Work::Work {
            waiting: BTreeSet::new(),
            current,
        }
    });
    result
}

pub fn status<V: Clone>(
    state: &State<V>,
    runtime: &impl Runtime<V>,
    slot: &Slot,
    object: Object,
) -> Status<V> {
    let objects = class(state, slot);
    let Some(info) = objects.vals.get(&object) else {
        return Status::Sleep;
    };
    match info.comp.get(slot) {
        Some(Work::Work { .. }) => Status::Awoke,
        Some(Work::Done) => Status::Ready(info.data.clone()),
        None => {
            let value = runtime.current(state, slot, object);
            if runtime.slot_is_empty(slot, &value) {
                Status::Sleep
            } else {
                Status::Ready(info.data.clone())
            }
        }
    }
}

fn collect_inner<V: Clone>(
    mut state: State<V>,
    runtime: &impl Runtime<V>,
    slot: &Slot,
    object: Object,
    promises: Vec<Pid>,
) -> Result<State<V>, String> {
    let was = runtime.current(&state, slot, object);
    for pid in promises {
        enter_promise(&mut state, runtime, slot, object, pid);
        state = runtime.run(state, slot, object, pid)?;
        leave_promise(&mut state, runtime, slot, object, pid);
    }
    let waiting = dequeue_waiting(&mut state, runtime, slot, object);
    if waiting.is_empty() {
        return Ok(state);
    }
    let now = runtime.current(&state, slot, object);
    match runtime.order(slot, &now, &was) {
        Order::Equal | Order::Less => Ok(state),
        Order::Greater | Order::Incomparable => {
            collect_inner(state, runtime, slot, object, waiting)
        }
    }
}

pub fn collect<V: Clone>(
    mut state: State<V>,
    runtime: &impl Runtime<V>,
    slot: &Slot,
    object: Object,
) -> Result<(State<V>, V), String> {
    if object == 0 {
        let value = runtime.current(&state, slot, object);
        return Ok((state, value));
    }
    match status(&state, runtime, slot, object) {
        Status::Ready(_) => {}
        Status::Awoke => enqueue_promises(&mut state, runtime, slot, object),
        Status::Sleep => {
            enter_slot(&mut state, runtime, slot, object);
            state = collect_inner(state, runtime, slot, object, runtime.initial_promises(slot))?;
            leave_slot(&mut state, runtime, slot, object);
        }
    }
    let value = runtime.current(&state, slot, object);
    Ok((state, value))
}

pub fn set_package<V>(mut state: State<V>, package: impl Into<String>) -> State<V> {
    state.package = package.into();
    state
}

pub fn import<V: Clone>(
    mut state: State<V>,
    imports: &[String],
    strict: bool,
) -> Result<State<V>, String> {
    let package = state.package.clone();
    for input in imports {
        let (wanted_package, wanted_symbol) = input
            .split_once(':')
            .map_or((input.as_str(), ""), |(p, s)| (p, s));
        let mut found = false;
        for class_name in state.classes.keys().cloned().collect::<Vec<_>>() {
            let mut objects = class(&state, &class_name);
            let names = objects
                .vals
                .values()
                .filter_map(|info| info.name.clone())
                .collect::<Vec<_>>();
            for symbol in names {
                let matches = if wanted_symbol.is_empty() {
                    symbol.package == wanted_package
                        && objects
                            .pubs
                            .get(&symbol.package)
                            .is_some_and(|pubs| pubs.contains(&objects.objs[&symbol]))
                } else {
                    symbol.package == wanted_package && symbol.name == wanted_symbol
                };
                if matches {
                    found = true;
                    let object = objects.objs[&symbol];
                    if strict
                        && objects
                            .objs
                            .get(&FullName::new(&package, &symbol.name))
                            .is_some_and(|old| *old != object)
                    {
                        return Err(format!("import conflict for {}", symbol.show()));
                    }
                    objects
                        .objs
                        .insert(FullName::new(&package, &symbol.name), object);
                }
            }
            state.classes.insert(class_name, objects);
        }
        if !found {
            return Err(format!("unknown package or symbol {input}"));
        }
    }
    Ok(state)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Default)]
    struct TestRuntime {
        promises: BTreeMap<Slot, Vec<Pid>>,
    }
    impl Runtime<Option<i64>> for TestRuntime {
        fn empty_record(&self) -> Option<i64> {
            None
        }
        fn current(&self, state: &State<Option<i64>>, slot: &Slot, object: Object) -> Option<i64> {
            class(state, slot)
                .vals
                .get(&object)
                .and_then(|info| info.data)
        }
        fn slot_is_empty(&self, _slot: &Slot, value: &Option<i64>) -> bool {
            value.is_none()
        }
        fn order(&self, _slot: &Slot, left: &Option<i64>, right: &Option<i64>) -> Order {
            match (left, right) {
                (Some(left), Some(right)) if left > right => Order::Greater,
                (Some(left), Some(right)) if left < right => Order::Less,
                (Some(_), Some(_)) => Order::Equal,
                (Some(_), None) => Order::Greater,
                (None, Some(_)) => Order::Less,
                (None, None) => Order::Equal,
            }
        }
        fn initial_promises(&self, slot: &Slot) -> Vec<Pid> {
            self.promises.get(slot).cloned().unwrap_or_default()
        }
        fn run(
            &self,
            state: State<Option<i64>>,
            slot: &Slot,
            object: Object,
            pid: Pid,
        ) -> Result<State<Option<i64>>, String> {
            let current = self.current(&state, slot, object).unwrap_or(0);
            provide(state, self, slot, object, &Some(current + pid as i64))
        }
        fn commit(
            &self,
            _state: &State<Option<i64>>,
            _slot: &Slot,
            old: Option<&Option<i64>>,
            value: &Option<i64>,
        ) -> Result<Option<i64>, String> {
            match (old, value) {
                (Some(Some(left)), Some(right)) => Ok(Some((*left).max(*right))),
                _ => Ok(*value),
            }
        }
    }

    #[test]
    fn fixed_point_and_identity() {
        let slot = Slot::new("test", "x");
        let runtime = TestRuntime {
            promises: BTreeMap::from([(slot.clone(), vec![1, 2])]),
        };
        let (state, object) = create(State::default(), &slot);
        let (state, value) = collect(state, &runtime, &slot, object).unwrap();
        assert_eq!(value, Some(3));
        let (state, _) = create(state, &slot);
        assert_ne!(object, create(State::<Option<i64>>::default(), &slot).1);
        assert_eq!(objects(&state, &slot).len(), 1);
    }

    #[test]
    fn null_is_empty_and_intern_is_stable() {
        let slot = Slot::new("test", "x");
        let runtime = TestRuntime::default();
        let (state, object) = create(State::default(), &slot);
        let (state, first) = intern(state, &slot, FullName::new("user", "main"), true, &None);
        let (state, second) = intern(state, &slot, FullName::new("user", "main"), true, &None);
        assert_eq!(first, second);
        assert_eq!(repr(&state, &slot, first), "main");
        assert_eq!(collect(state, &runtime, &slot, 0).unwrap().1, None);
        assert_ne!(object, first);
    }
}
