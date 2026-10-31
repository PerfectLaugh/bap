import Std

namespace Bap.Emu

def shouldShareMemory (processes : Std.HashMap Nat α) (current next : Nat) : Bool :=
  !(processes.contains current || processes.contains next)

def selectMemory (processes : Std.HashMap Nat β) (current next : Nat)
    (currentMemory targetMemory : α) : α :=
  if shouldShareMemory processes current next then currentMemory else targetMemory

def controlledStopped (control : Std.HashMap Nat Bool) (id : Nat) (fallback : Bool) : Bool :=
  (control.get? id).getD fallback

theorem shouldShareMemory_comm (processes : Std.HashMap Nat α) (current next : Nat) :
    shouldShareMemory processes current next = shouldShareMemory processes next current := by
  unfold shouldShareMemory
  cases processes.contains current <;> cases processes.contains next <;> rfl

theorem shouldShareMemory_private_current (processes : Std.HashMap Nat α) (current next : Nat)
    (h : processes.contains current = true) : shouldShareMemory processes current next = false := by
  simp [shouldShareMemory, h]

theorem shouldShareMemory_private_next (processes : Std.HashMap Nat α) (current next : Nat)
    (h : processes.contains next = true) : shouldShareMemory processes current next = false := by
  simp [shouldShareMemory, h]

theorem shouldShareMemory_shared (processes : Std.HashMap Nat α) (current next : Nat)
    (currentPrivate : processes.contains current = false) (nextPrivate : processes.contains next = false) :
    shouldShareMemory processes current next = true := by
  simp [shouldShareMemory, currentPrivate, nextPrivate]

theorem selectMemory_private_current (processes : Std.HashMap Nat β) (current next : Nat)
    (currentMemory targetMemory : α) (h : processes.contains current = true) :
    selectMemory processes current next currentMemory targetMemory = targetMemory := by
  simp [selectMemory, shouldShareMemory_private_current processes current next h]

theorem selectMemory_private_next (processes : Std.HashMap Nat β) (current next : Nat)
    (currentMemory targetMemory : α) (h : processes.contains next = true) :
    selectMemory processes current next currentMemory targetMemory = targetMemory := by
  simp [selectMemory, shouldShareMemory_private_next processes current next h]

theorem selectMemory_shared (processes : Std.HashMap Nat β) (current next : Nat)
    (currentMemory targetMemory : α)
    (currentPrivate : processes.contains current = false) (nextPrivate : processes.contains next = false) :
    selectMemory processes current next currentMemory targetMemory = currentMemory := by
  simp [selectMemory, shouldShareMemory_shared processes current next currentPrivate nextPrivate]

theorem controlledStopped_default (control : Std.HashMap Nat Bool) (id : Nat) (fallback : Bool)
    (h : control.get? id = none) : controlledStopped control id fallback = fallback := by
  unfold controlledStopped
  rw [h]
  rfl

theorem controlledStopped_stop (control : Std.HashMap Nat Bool) (id : Nat) (fallback : Bool)
    (h : control.get? id = some true) : controlledStopped control id fallback = true := by
  unfold controlledStopped
  rw [h]
  rfl

theorem controlledStopped_resume (control : Std.HashMap Nat Bool) (id : Nat) (fallback : Bool)
    (h : control.get? id = some false) : controlledStopped control id fallback = false := by
  unfold controlledStopped
  rw [h]
  rfl

end Bap.Emu
