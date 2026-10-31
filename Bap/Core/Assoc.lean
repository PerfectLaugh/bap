import Std

namespace Bap.Assoc

def get [DecidableEq α] (key : α) (entries : List (α × β)) : Option β :=
  List.lookup key entries

def put [DecidableEq α] (key : α) (value : β) (entries : List (α × β)) : List (α × β) :=
  (key, value) :: entries.filter fun entry => entry.1 != key

def remove [DecidableEq α] (key : α) (entries : List (α × β)) : List (α × β) :=
  entries.filter fun entry => entry.1 != key

def keys (entries : List (α × β)) : List α := entries.map Prod.fst

@[simp] theorem get_nil [DecidableEq α] (key : α) : get key ([] : List (α × β)) = none := by
  rfl

@[simp] theorem get_put_same [DecidableEq α] (key : α) (value : β) (entries : List (α × β)) :
    get key (put key value entries) = some value := by
  simp [get, put]

end Bap.Assoc
