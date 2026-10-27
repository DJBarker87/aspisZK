import R1Z.PV_CBL_DigestUpdateStep
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_DigestUpdateModel
set_option autoImplicit false
abbrev Snapshot := PV_CBL_DigestUpdateStep.Snapshot
def step (q : Snapshot) (byte : U8) : Snapshot :=
  PV_CBL_DigestUpdateStep.next q.1 q.2.1 q.2.2.1 q.2.2.2 byte
def value (q : Snapshot) (bytes : List U8) : Snapshot := bytes.foldl step q
theorem append (q : Snapshot) (a b : List U8) : value q (a++b)=value (value q a) b :=
  List.foldl_append
theorem drop_step {T : Type} (xs : List T) (i : Nat) (hi : i<xs.length) :
    xs.drop i=xs[i]::xs.drop (i+1) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i (by simpa using hi)
#print axioms step
#print axioms value
#print axioms append
#print axioms drop_step
end R1Z.PV_CBL_DigestUpdateModel
