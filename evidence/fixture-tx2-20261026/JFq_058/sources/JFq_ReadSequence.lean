import JFq_Scalar
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFq_ReadSequence
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port5Q2_ReaderWeights

theorem append (read : CheckpointBytes4Sections.ReadK) (bytes : Slice U8)
    (m n : Nat) (start : Usize) :
    reads read bytes (m+n) start = (do
      let first ← reads read bytes m start
      match first with
      | .Err e => ok (.Err e)
      | .Ok (xs,middle) => do
        let second ← reads read bytes n middle
        match second with
        | .Err e => ok (.Err e)
        | .Ok (ys,last) => ok (.Ok (xs++ys,last))) := by
  induction m generalizing start with
  | zero => simp only [Nat.zero_add,reads,bind_tc_ok,Aeneas.Std.uncurry,List.nil_append]
  | succ m ih =>
    simp only [Nat.succ_add,reads,ih,bind_assoc_eq]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    rintro ⟨value,out⟩ called
    cases value with
    | Err e => rfl
    | Ok x =>
      simp only [Aeneas.Std.uncurry,bind_tc_ok,bind_assoc_eq]
      apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro first calledFirst
      cases first with
      | Err e => rfl
      | Ok pair =>
        rcases pair with ⟨xs,middle⟩
        simp only [Aeneas.Std.uncurry,bind_tc_ok,bind_assoc_eq]
        apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro second calledSecond
        cases second with
        | Err e => rfl
        | Ok pair => cases pair; rfl

theorem join (read : CheckpointBytes4Sections.ReadK) (bytes : Slice U8)
    (m n : Nat) (start middle last : Usize) (xs ys : List K)
    (left : reads read bytes m start=ok (.Ok (xs,middle)))
    (right : reads read bytes n middle=ok (.Ok (ys,last))) :
    reads read bytes (m+n) start=ok (.Ok (xs++ys,last)) := by
  rw [append,left]
  simp only [bind_tc_ok,Aeneas.Std.uncurry,right]

#print axioms append
#print axioms join
end AspisR1.JFq_ReadSequence
end
