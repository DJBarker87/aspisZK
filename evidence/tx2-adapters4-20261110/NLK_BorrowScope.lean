import NLK_ParentFold
import NLA_RootPrefix
set_option autoImplicit false
namespace NLK_BorrowScope
open Aeneas Aeneas.Std Result NLF_ParentModel NLF_SdkModel
/-- A prefix is retained even when the child aborts or diverges. A returning
Err is a returned value and performs lexical Drop; fail/div do not fabricate it. -/
structure Outcome (A : Type) where
  parent : Parent
  result : Result (Except ProgramError A)

/-- Local support: a callback is permitted here only as an intermediate child
packet. A row root must instantiate it with the CLOSED SAME-payload child. -/
def run {A : Type} (p : Parent) (account : Nat)
    (child : Payload → Result (Except ProgramError A)) : Outcome A :=
  let acq := acquire p account .shared
  match acq.2 with
  | .error e => ⟨acq.1, .ok (.error e)⟩
  | .ok guard =>
    let read := NLF_ParentModel.deref acq.1 guard
    match read.2 with
    | .error _ => ⟨read.1,.fail .panic⟩
    | .ok bytes =>
      match child bytes with
      | .ok reply =>
        let dropped := NLF_ParentModel.release read.1 guard
        match dropped.2 with
        | .ok _ => ⟨dropped.1,.ok reply⟩
        | .error _ => ⟨dropped.1,.fail .panic⟩
      | .fail e => ⟨read.1,.fail e⟩
      | .div => ⟨read.1,.div⟩

/-- Every prefix preserves global live-token ownership, including abort. -/
theorem invariant {A : Type} (p : Parent) (account : Nat)
    (child : Payload → Result (Except ProgramError A)) (valid : Invariant p) :
    Invariant (run p account child).parent := by
  have ha := acquire_preserves p account .shared valid
  unfold run
  split
  · exact ha
  · rename_i guard hg
    have hd := deref_invariant (acquire p account .shared).1 guard ha
    split
    · exact hd
    · rename_i bytes hb
      split
      · have hr := release_preserves (NLF_ParentModel.deref (acquire p account .shared).1 guard).1 guard hd
        split <;> exact hr
      · exact hd
      · exact hd

#print invariant
#print axioms invariant
end NLK_BorrowScope
