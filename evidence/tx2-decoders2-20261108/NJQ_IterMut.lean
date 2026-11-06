import NJQ_Read
set_option autoImplicit false
namespace NJQ_IterMut
/-- Library lens for the uncons operation of a valid mutable slice iterator.
The original allocation prefix is owned by the enclosing loop frame. -/
def next {T : Type} (xs : List T) : Option (T × List T × (T → List T → List T)) :=
 match xs with
 | [] => none
 | x::rest => some (x,rest,fun value tail=>value::tail)

theorem exhausted {T : Type} : next ([] : List T)=none := rfl

theorem entered {T : Type} (x : T) (rest : List T) :
 next (x::rest)=some (x,rest,fun value tail=>value::tail) := rfl

/-- Returning the borrowed head writes only that cell; no immutable suffix loss. -/
theorem writeback_frame {T : Type} (prefix : List T) (x value : T) (rest : List T) :
 (prefix ++ (fun value tail=>value::tail) value rest).take prefix.length=prefix ∧
 (prefix ++ (fun value tail=>value::tail) value rest).drop (prefix.length+1)=rest := by
 constructor
 · simp
 · simp

#print axioms exhausted
#print axioms entered
#print axioms writeback_frame
end NJQ_IterMut
