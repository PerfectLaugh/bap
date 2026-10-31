import Bap.Emu.Task

namespace Bap.Emu.TaskTable

/-! `poll` says what `waitpid` may say and nothing else, a process isn't over while a thread of it runs, what `exitGroup`
leaves is what a parent finds, a child is reported once, and no child is left with a parent that is gone. -/

private theorem report_some {table : TaskTable} {leader : Task} {pid status : Nat}
    (h : table.report leader = some (pid, status)) :
    table.alone leader = true ∧ leader.tid = pid ∧ leader.status = some status := by
  simp only [report] at h
  split at h
  · next halone =>
    cases hs : leader.status with
    | none => simp [hs] at h
    | some value =>
      simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨halone, h.1, by rw [h.2]⟩
  · cases h

/-- What is reported is the leader of a child of the one that asks, of those it asked for, it did exit with that status,
and no other task of it is left. -/
theorem poll_exited {table : TaskTable} {parent : Nat} {target : Option Nat} {pid status : Nat}
    (h : table.poll parent target = .exited pid status) :
    ∃ task ∈ table.tasks, task.tid = pid ∧ task.parent = parent ∧ task.status = some status ∧
      asked parent target task = true ∧ table.alone task = true := by
  simp only [poll] at h
  split at h
  · next hsome =>
    simp only [WaitResult.exited.injEq] at h
    obtain ⟨hp, hs⟩ := h
    subst hp hs
    obtain ⟨task, hmem, hreport⟩ := List.exists_of_findSome?_eq_some hsome
    obtain ⟨hin, hasked⟩ := List.mem_filter.mp hmem
    obtain ⟨halone, hpid, hstatus⟩ := report_some hreport
    refine ⟨task, hin, hpid, ?_, hstatus, hasked, halone⟩
    simp only [asked, Bool.and_eq_true, beq_iff_eq] at hasked
    exact hasked.1.2
  · split at h <;> cases h

/-- A process isn't over while another of its tasks runs. -/
theorem poll_thread_left {table : TaskTable} {parent : Nat} {target : Option Nat} {pid status : Nat} {other : Task}
    (hother : other ∈ table.tasks) (hgroup : other.group = pid) (htid : other.tid ≠ pid) (hlive : other.status = none) :
    table.poll parent target ≠ .exited pid status := by
  intro h
  obtain ⟨task, _, hpid, _, _, hasked, halone⟩ := poll_exited h
  simp only [asked, Bool.and_eq_true, beq_iff_eq] at hasked
  have hleader : task.group = pid := by rw [← hasked.1.1, hpid]
  have := List.all_eq_true.mp halone other hother
  simp [hgroup, hleader, hpid, htid, hlive] at this

/-- `noChild` means that none is what was asked for. -/
theorem poll_noChild_iff (table : TaskTable) (parent : Nat) (target : Option Nat) :
    table.poll parent target = .noChild ↔ ∀ task ∈ table.tasks, asked parent target task = false := by
  simp only [poll]
  constructor
  · intro h task hmem
    split at h
    · cases h
    · split at h
      · next hempty =>
        cases hasked : asked parent target task
        · rfl
        · have : task ∈ table.tasks.filter (asked parent target) := List.mem_filter.mpr ⟨hmem, hasked⟩
          simp [List.isEmpty_iff.mp hempty] at this
      · cases h
  · intro h
    have hempty : table.tasks.filter (asked parent target) = [] := by
      rw [List.filter_eq_nil_iff]
      intro task hmem
      simp [h task hmem]
    simp [hempty]

/-- `running` means that some child was asked for, and that none of those can be reported. -/
theorem poll_running {table : TaskTable} {parent : Nat} {target : Option Nat}
    (h : table.poll parent target = .running) :
    (∃ task ∈ table.tasks, asked parent target task = true) ∧
      ∀ task ∈ table.tasks, asked parent target task = true → table.report task = none := by
  simp only [poll] at h
  split at h
  · cases h
  · next hnone =>
    split at h
    · cases h
    · next hempty =>
      constructor
      · cases hfilter : table.tasks.filter (asked parent target) with
        | nil => simp [hfilter] at hempty
        | cons head tail =>
          have hmem : head ∈ table.tasks.filter (asked parent target) := by simp [hfilter]
          exact ⟨head, (List.mem_filter.mp hmem).1, (List.mem_filter.mp hmem).2⟩
      · intro task hmem hasked
        rw [List.findSome?_eq_none_iff] at hnone
        exact hnone task (List.mem_filter.mpr ⟨hmem, hasked⟩)

@[simp] private theorem exited_tid (group status init : Nat) (task : Task) : (exited group status init task).tid = task.tid := by
  simp only [exited]
  split
  · rfl
  · split <;> rfl

private theorem asked_other {parent pid : Nat} {task : Task} (h : task.tid ≠ pid) : asked parent (some pid) task = false := by
  simp [asked, h]

private theorem filter_exited {group status init parent : Nat} {leader : Task} (hleader : leader.tid = group)
    (hgroup : leader.group = group) (hparent : leader.parent = parent) :
    ∀ (tasks : List Task), (tasks.map (·.tid)).Nodup → leader ∈ tasks →
      (tasks.map (exited group status init)).filter (asked parent (some group)) = [{ leader with status := some status }] := by
  intro tasks
  induction tasks with
  | nil => intro _ h; cases h
  | cons head tail ih =>
    intro hnodup hmem
    simp only [List.map_cons, List.nodup_cons] at hnodup
    obtain ⟨hhead, htail⟩ := hnodup
    rw [List.map_cons, List.filter_cons]
    rcases List.mem_cons.mp hmem with rfl | hin
    · have hrest : (tail.map (exited group status init)).filter (asked parent (some group)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro mapped hmapped
        obtain ⟨task, htask, rfl⟩ := List.mem_map.mp hmapped
        have hne : task.tid ≠ group := by
          intro hsame
          exact hhead (by rw [hleader, ← hsame]; exact List.mem_map_of_mem htask)
        simp [asked_other (show (exited group status init task).tid ≠ group by rw [exited_tid]; exact hne)]
      simp [hgroup, hleader, hrest, exited, asked, hparent]
    · have hne : head.tid ≠ group := by
        intro hsame
        exact hhead (by rw [hsame, ← hleader]; exact List.mem_map_of_mem hin)
      have hfalse : asked parent (some group) (exited group status init head) = false :=
        asked_other (by rw [exited_tid]; exact hne)
      simp [hfalse, ih htail hin]

/-- A parent that waits for a child that has exited finds its status, when the ids of the table are different. -/
theorem poll_after_exitGroup {table : TaskTable} {pid parent status init : Nat}
    (hnodup : (table.tasks.map (·.tid)).Nodup) {leader : Task} (hmem : leader ∈ table.tasks)
    (hpid : leader.tid = pid) (hgroup : leader.group = pid) (hparent : leader.parent = parent) :
    (table.exitGroup pid status init).poll parent (some pid) = .exited pid status := by
  have hfilter := filter_exited (status := status) (init := init) hpid hgroup hparent table.tasks hnodup hmem
  have halone : (table.exitGroup pid status init).alone { leader with status := some status } = true := by
    simp only [alone, exitGroup, List.all_eq_true, List.mem_map]
    rintro other ⟨task, _, rfl⟩
    by_cases hg : task.group = pid
    · simp [exited, hg]
    · have hsame : (exited pid status init task).group = task.group := by
        simp only [exited, show (task.group == pid) = false by simpa using hg, Bool.false_eq_true, ↓reduceIte]
        split <;> rfl
      simp [hsame, hgroup, hg]
  have hf : (table.exitGroup pid status init).tasks.filter (asked parent (some pid)) =
      [{ leader with status := some status }] := hfilter
  simp only [poll, hf, List.findSome?_cons, report, halone]
  simp [hpid]

/-- A child that was reported is gone: nothing can report it again. -/
theorem poll_after_reap (table : TaskTable) (pid parent other status : Nat) :
    (table.reap pid).poll parent (some pid) ≠ .exited other status := by
  intro h
  obtain ⟨task, hmem, _, _, _, hasked, _⟩ := poll_exited h
  have hkept := (List.mem_filter.mp hmem).2
  simp only [asked, Bool.and_eq_true, beq_iff_eq] at hasked
  have : task.group = pid := by rw [← hasked.1.1, hasked.2]
  simp [this] at hkept

/-- Nothing outside the group that exited keeps it as a parent. -/
theorem exitGroup_reparents (table : TaskTable) {pid status init : Nat} (hinit : init ≠ pid) :
    ∀ task ∈ (table.exitGroup pid status init).tasks, task.group ≠ pid → task.parent ≠ pid := by
  intro task hmem hgroup hparent
  simp only [exitGroup, List.mem_map] at hmem
  obtain ⟨original, _, rfl⟩ := hmem
  by_cases hg : original.group = pid
  · simp [exited, hg] at hgroup
  · simp only [exited, show (original.group == pid) = false by simpa using hg, Bool.false_eq_true, ↓reduceIte] at hparent hgroup
    split at hparent
    · exact hinit hparent
    · next hq => exact hq (by simpa using hparent)

/-- A process that exited leaves no waiter behind. -/
theorem exitGroup_no_waiter (table : TaskTable) {pid status init : Nat} {task : Task} :
    ∀ waiter ∈ (table.exitGroup pid status init).waiters, table.find? waiter.thread = some task → task.group ≠ pid := by
  intro waiter hmem hfind
  simp only [exitGroup] at hmem
  have := (List.mem_filter.mp hmem).2
  simp only [hfind] at this
  simpa using this

/-- A new task has the space it was made with: that of its parent for a thread, and its own for a process. -/
theorem spaceOf_addTask (table : TaskTable) (task : Task) (hfresh : ∀ other ∈ table.tasks, other.tid ≠ task.tid) :
    (table.addTask task).spaceOf task.tid = task.space := by
  have hnone : table.tasks.find? (·.tid == task.tid) = none := by
    rw [List.find?_eq_none]
    intro other hother
    simpa using hfresh other hother
  simp [spaceOf, find?, addTask, List.find?_append, hnone]

/-- Settling wakes no waiter that isn't there. -/
theorem settle_woken_mem (table : TaskTable) :
    ∀ entry ∈ table.settle.2, entry.1 ∈ table.waiters := by
  have step : ∀ (waiters : List Waiter) (start : TaskTable × List (Waiter × WaitResult)),
      ∀ entry ∈ (waiters.foldl settleOne start).2, entry ∈ start.2 ∨ entry.1 ∈ waiters := by
    intro waiters
    induction waiters with
    | nil => intro start entry hmem; exact Or.inl hmem
    | cons head tail ih =>
      intro start entry hmem
      rw [List.foldl_cons] at hmem
      rcases ih _ entry hmem with hin | hin
      · obtain ⟨table, woken⟩ := start
        simp only [settleOne] at hin
        split at hin
        · exact Or.inl hin
        · rcases List.mem_append.mp hin with hold | hnew
          · exact Or.inl hold
          · simp only [List.mem_singleton] at hnew
            exact Or.inr (by simp [hnew])
        · rcases List.mem_append.mp hin with hold | hnew
          · exact Or.inl hold
          · simp only [List.mem_singleton] at hnew
            exact Or.inr (by simp [hnew])
      · exact Or.inr (List.mem_cons_of_mem _ hin)
  intro entry hmem
  rcases step _ _ entry hmem with hin | hin
  · simp at hin
  · exact hin

end Bap.Emu.TaskTable

namespace Bap.Emu

/-- What a status says of the code it holds, as `WEXITSTATUS` reads it, and that `WIFEXITED` holds. -/
theorem exitedStatus_code (code : Nat) : exitedStatus code / 256 = code % 256 ∧ exitedStatus code % 128 = 0 := by
  simp only [exitedStatus]
  omega

/-- A signal, as `WTERMSIG` reads it, and what `WIFEXITED` tells from an exit. -/
theorem signaledStatus_signal {signal : Nat} (h : signal % 128 ≠ 0) :
    signaledStatus signal % 128 = signal % 128 ∧ signaledStatus signal % 128 ≠ 0 := by
  simp only [signaledStatus]
  omega

/-- The word of -1 asks for any child. -/
theorem waitTarget_any (width : Nat) : waitTarget width (2 ^ width - 1) = some none := by
  simp [waitTarget]

/-- Only a positive word asks for one process, and it asks for that one. -/
theorem waitTarget_one {width target pid : Nat} (h : waitTarget width target = some (some pid)) :
    pid = target ∧ 0 < target ∧ target < 2 ^ (width - 1) := by
  simp only [waitTarget] at h
  split at h
  · cases h
  · split at h
    · next hrange =>
      simp only [Option.some.injEq] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hrange
      exact ⟨h.symm, hrange⟩
    · cases h

/-- Nothing runs but a thread that isn't stopped, with fuel left. -/
theorem scheduleStep_run {current fuel : Nat} {stopped blocked : Bool} {next : Option Nat} {waiting : List Nat}
    {first : Option Nat} (h : scheduleStep current fuel stopped blocked next waiting first = .run) :
    stopped = false ∧ fuel ≠ 0 := by
  cases stopped with
  | true =>
    simp only [scheduleStep, ite_true] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h <;> cases h
  | false =>
    simp only [scheduleStep, Bool.false_eq_true, ite_false] at h
    split at h
    · cases h
    · next hfuel => exact ⟨rfl, by simpa using hfuel⟩

/-- A breakpoint isn't taken from the one who asked: a thread that stopped for a reason of its own stays current. -/
theorem scheduleStep_own_stop (current fuel : Nat) (next : Option Nat) (waiting : List Nat) (first : Option Nat) :
    scheduleStep current fuel true false next waiting first = .done (.stopped current) := rfl

/-- The scheduler moves on from a blocked thread to the next that can run, and to nothing else. -/
theorem scheduleStep_switch {current fuel id : Nat} {stopped blocked : Bool} {next : Option Nat} {waiting : List Nat}
    {first : Option Nat} (h : scheduleStep current fuel stopped blocked next waiting first = .switch id) :
    stopped = true ∧ blocked = true ∧ next = some id := by
  cases stopped with
  | false =>
    simp only [scheduleStep, Bool.false_eq_true, ite_false] at h
    split at h <;> cases h
  | true =>
    cases blocked with
    | false => simp [scheduleStep] at h
    | true =>
      cases next with
      | some other =>
        simp only [scheduleStep, ite_true, Bool.not_true, Bool.false_eq_true, ite_false, ScheduleStep.switch.injEq] at h
        exact ⟨rfl, rfl, by rw [h]⟩
      | none =>
        simp only [scheduleStep, ite_true, Bool.not_true, Bool.false_eq_true, ite_false] at h
        split at h
        · cases h
        · split at h <;> cases h

/-- A deadlock is what it says: the thread that runs can't, nor can any other, and these are the ones that wait. -/
theorem scheduleStep_deadlock {current fuel : Nat} {stopped blocked : Bool} {next : Option Nat} {waiting found : List Nat}
    {first : Option Nat} (h : scheduleStep current fuel stopped blocked next waiting first = .done (.deadlock found)) :
    stopped = true ∧ blocked = true ∧ next = none ∧ found = waiting ∧ waiting ≠ [] := by
  cases stopped with
  | false =>
    simp only [scheduleStep, Bool.false_eq_true, ite_false] at h
    split at h <;> cases h
  | true =>
    cases blocked with
    | false => simp [scheduleStep] at h
    | true =>
      cases next with
      | some other => simp [scheduleStep] at h
      | none =>
        simp only [scheduleStep, ite_true, Bool.not_true, Bool.false_eq_true, ite_false] at h
        split at h
        · next hwait =>
          simp only [ScheduleStep.done.injEq, ScheduleOutcome.deadlock.injEq] at h
          refine ⟨rfl, rfl, rfl, h.symm, ?_⟩
          intro hnil
          simp [hnil] at hwait
        · split at h <;> cases h

/-- A run is finished only when nothing can run, nothing waits, and the first process has its status. -/
theorem scheduleStep_finished {current fuel status : Nat} {stopped blocked : Bool} {next : Option Nat} {waiting : List Nat}
    {first : Option Nat} (h : scheduleStep current fuel stopped blocked next waiting first = .done (.finished status)) :
    stopped = true ∧ blocked = true ∧ next = none ∧ waiting = [] ∧ first = some status := by
  cases stopped with
  | false =>
    simp only [scheduleStep, Bool.false_eq_true, ite_false] at h
    split at h <;> cases h
  | true =>
    cases blocked with
    | false => simp [scheduleStep] at h
    | true =>
      cases next with
      | some other => simp [scheduleStep] at h
      | none =>
        simp only [scheduleStep, ite_true, Bool.not_true, Bool.false_eq_true, ite_false] at h
        split at h
        · cases h
        · next hwait =>
          cases first with
          | none => cases h
          | some value =>
            simp only [ScheduleStep.done.injEq, ScheduleOutcome.finished.injEq] at h
            exact ⟨rfl, rfl, rfl, by simpa using hwait, by rw [h]⟩

end Bap.Emu
