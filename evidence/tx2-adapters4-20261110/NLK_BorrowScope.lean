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
  dsimp only [run]
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

/-- Returned borrow failure performs no dereference or child call. -/
theorem acquire_error {A : Type} (p : Parent) (account : Nat)
    (child : Payload → Result (Except ProgramError A)) (e : ProgramError)
    (cut : (acquire p account .shared).2 = .error e) :
    run p account child = ⟨(acquire p account .shared).1,.ok (.error e)⟩ := by
  simp only [run,cut]

/-- An abort inside the borrowed call preserves the live-guard prefix. -/
theorem child_abort {A : Type} (p : Parent) (account : Nat)
    (child : Payload → Result (Except ProgramError A))
    (guard : NLF_RefCell.Guard) (bytes : Payload) (e : Error)
    (acq : (acquire p account .shared).2 = .ok guard)
    (read : (NLF_ParentModel.deref (acquire p account .shared).1 guard).2 = .ok bytes)
    (abort : child bytes = .fail e) :
    run p account child =
      ⟨(NLF_ParentModel.deref (acquire p account .shared).1 guard).1,.fail e⟩ := by
  simp only [run,acq,read,abort]

/-- Divergence likewise has no fabricated release event. -/
theorem child_divergence {A : Type} (p : Parent) (account : Nat)
    (child : Payload → Result (Except ProgramError A))
    (guard : NLF_RefCell.Guard) (bytes : Payload)
    (acq : (acquire p account .shared).2 = .ok guard)
    (read : (NLF_ParentModel.deref (acquire p account .shared).1 guard).2 = .ok bytes)
    (diverges : child bytes = .div) :
    run p account child =
      ⟨(NLF_ParentModel.deref (acquire p account .shared).1 guard).1,.div⟩ := by
  simp only [run,acq,read,diverges]

#print axioms acquire_error
#print axioms child_abort
#print axioms child_divergence

/-- Both returned child variants perform the SAME lexical release; this
lemma intentionally keeps the small step cuts local rather than a row root. -/
theorem child_returned {A : Type} (p : Parent) (account : Nat)
    (child : Payload → Result (Except ProgramError A))
    (guard : NLF_RefCell.Guard) (bytes : Payload) (reply : Except ProgramError A)
    (acq : (acquire p account .shared).2 = .ok guard)
    (read : (NLF_ParentModel.deref (acquire p account .shared).1 guard).2 = .ok bytes)
    (returned : child bytes = .ok reply)
    (dropped : (NLF_ParentModel.release
      (NLF_ParentModel.deref (acquire p account .shared).1 guard).1 guard).2 = .ok ()) :
    run p account child =
      ⟨(NLF_ParentModel.release
        (NLF_ParentModel.deref (acquire p account .shared).1 guard).1 guard).1,.ok reply⟩ := by
  simp only [run,acq,read,returned,dropped]
#print axioms child_returned

#print invariant
#print axioms invariant
end NLK_BorrowScope
