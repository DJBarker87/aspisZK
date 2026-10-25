import T2Nat_WeightLoop
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_WeightSequence
open Aeneas Aeneas.Std Result AspisR1Stage2
open CheckpointBytes4Sections
abbrev K := aspis_core.field.QM31

def restored (bytes : Slice U8)
    (value : core.result.Result (List K × Usize) verifier.Error) :
    Result (core.result.Result (List K × verifier.Reader) verifier.Error) :=
  match value with
  | .Err e => ok (.Err e)
  | .Ok (xs,last) => ok (.Ok (xs,⟨bytes,last⟩))

/-- Full sequence equality, including each rejection position. The backing
bytes are derived from each executed scalar read, not assumed per iteration. -/
theorem sequence (bytes : Slice U8) (n : Nat) (start : Usize) :
    readList CheckpointBytes3Reader.readK n ⟨bytes,start⟩ =
      (do let value ← Port5Q2_ReaderWeights.reads CheckpointBytes3Reader.readK bytes n start
          restored bytes value) := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    simp only [readList,Port5Q2_ReaderWeights.reads,bind_assoc_eq]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro pair called
    rcases pair with ⟨value,out⟩
    cases value with
    | Err e => rfl
    | Ok x =>
      have frame := Port5Q2_ReaderFrame.readK ⟨bytes,start⟩ out (.Ok x) called
      have outEq : out=⟨bytes,out.at⟩ := by
        cases out
        simp only [verifier.Reader.mk.injEq]
        exact ⟨frame,True.intro⟩
      simp only [Aeneas.Std.uncurry]
      rw [outEq,ih]
      simp only [bind_assoc_eq]
      apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro rest returned
      cases rest with
      | Err e => rfl
      | Ok pair => rcases pair with ⟨xs,last⟩; rfl

/-- Emitted mutable helper and retained iterator have the same complete
Result on the same Vec, with the retained scalar implementation. -/
theorem weights (bytes : Slice U8) (start : Usize) (v : alloc.vec.Vec K) :
    Port5Q2_ReaderWeights.weights CheckpointBytes3Reader.readK bytes start v =
      CheckpointBytes4Ops.readWeights bytes start v := by
  rw [Port5Q2_ReaderWeights.exact]
  change _ = (do
    let result ← weightLoop CheckpointBytes3Reader.readK v.val.length
      ⟨bytes,start⟩ ⟨⟨v.val,v.property⟩,0⟩
    match result with
    | .Err e => ok (.Err e)
    | .Ok (it,r) => ok (.Ok (⟨it.slice.val,it.slice.property⟩,r.at)))
  rw [T2Nat_WeightLoop.normalize CheckpointBytes3Reader.readK v.val [] ⟨bytes,start⟩ v.property]
  rw [sequence]
  simp only [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro value called
  cases value with
  | Err e => rfl
  | Ok pair => rcases pair with ⟨xs,last⟩; rfl

/-- Native codecs compose through iterator/back and preserve returned error
values, physical output Vec and cursor on this very input. -/
theorem native (unwrap : T2Nat_RawJoin.Unwrap)
    (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b) (bytes : Slice U8) (start : Usize)
    (v : alloc.vec.Vec K) :
    T2Nat_ResultEq.EqOk
      (Port5Q2_ReaderWeights.weights (T2Nat_ScalarJoin.readK unwrap) bytes start v)
      (CheckpointBytes4Ops.readWeights bytes start v) := by
  rw [← weights]
  exact T2Nat_WeightsCongr.native unwrap unwrap_ok bytes start v

#print axioms sequence
#print axioms weights
#print axioms native
end AspisR1.T2Nat_WeightSequence
end
