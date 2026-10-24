import AspisR1S9ProductionPairCutV1.Funs
import S9ConstructorV3TauCoordinatesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualProcessKindTensorReachedV1
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]
abbrev Q := aspis_core.field.QM31
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev Scratch := alloc.vec.Vec Q
abbrev Powers := Array W 4#usize
abbrev Parts := Array W 7#usize
abbrev Outcome := core.result.Result Unit verifier.Error

private theorem bind_success {A B : Type} (m : Result A) (next : A → Result B) (out : B)
    (h : (do let x ← m; next x)=.ok out) : ∃ x, m=.ok x ∧ next x=.ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok x => exact ⟨x,rfl,h⟩

def rowOfKind (kind : Usize) : Usize :=
  if kind < 4#usize then Usize.wrapping_sub kind 1#usize
  else Usize.wrapping_sub kind 2#usize

/-- S2 derives exclusion of the D dense branch. The tensor input is the
actual mutable scratch borrow of this SAME accepted process_kind call. -/
theorem process_kind_success_reaches_tensor
    (self : weights.Weights) (kind : Usize) (alpha : Slice W) (f : Slice U8)
    (folds n : Usize) (ap0 ap1 : Powers) (scratch scratchOut : Scratch)
    (parts partsOut : Parts) (result : Outcome)
    (hs2 : self.variant=transport.Variant.S2)
    (hcall : weights.process_kind self kind alpha f folds n ap0 ap1 scratch parts =
      .ok (result,scratchOut,partsOut)) :
    ∃ tensorOut : Slice Q, weights.Weights.tensor self (rowOfKind kind) folds
      (alloc.vec.Vec.deref_mut scratch).1 = .ok tensorOut := by
  have hnotD : transport.Variant.Insts.CoreCmpPartialEqVariant.eq self.variant transport.Variant.D = .ok false := by
    rw [hs2]
    simp [transport.Variant.Insts.CoreCmpPartialEqVariant.eq,transport.Variant.read_discriminant]
  unfold weights.process_kind at hcall
  rw [hnotD] at hcall
  simp only [bind_tc_ok,Bool.false_eq_true,↓reduceIte] at hcall
  obtain ⟨row,hrow,hcall⟩ := bind_success _ _ _ hcall
  have hrowCall : (if kind < 4#usize then Result.ok (Usize.wrapping_sub kind 1#usize)
      else Result.ok (Usize.wrapping_sub kind 2#usize)) = Result.ok (rowOfKind kind) := by
    unfold rowOfKind
    split <;> rfl
  have hrowEq : row=rowOfKind kind := (Result.ok.inj (hrowCall.symm.trans hrow)).symm
  obtain ⟨pair,hborrow,hcall⟩ := bind_success _ _ _ hcall
  rcases pair with ⟨input,back⟩
  obtain ⟨tensorOut,htensor,hcall⟩ := bind_success _ _ _ hcall
  have hborrowEq : alloc.vec.Vec.deref_mut scratch=(input,back) := Result.ok.inj hborrow
  have hinput : (alloc.vec.Vec.deref_mut scratch).1=input := congrArg Prod.fst hborrowEq
  refine ⟨tensorOut,?_⟩
  rw [hinput,←hrowEq]
  exact htensor

theorem row_kind1 : rowOfKind 1#usize=0#usize := by
  unfold rowOfKind
  rw [if_pos (show (1#usize : Usize) < 4#usize from by decide)]
  apply UScalar.eq_of_val_eq
  rw [AspisR1S9ConstructorV3TauCoordinatesV1.wrapping_sub_natural _ _ (by decide)]
  rfl
theorem row_kind2 : rowOfKind 2#usize=1#usize := by
  unfold rowOfKind
  rw [if_pos (show (2#usize : Usize) < 4#usize from by decide)]
  apply UScalar.eq_of_val_eq
  rw [AspisR1S9ConstructorV3TauCoordinatesV1.wrapping_sub_natural _ _ (by decide)]
  rfl
theorem row_kind3 : rowOfKind 3#usize=2#usize := by
  unfold rowOfKind
  rw [if_pos (show (3#usize : Usize) < 4#usize from by decide)]
  apply UScalar.eq_of_val_eq
  rw [AspisR1S9ConstructorV3TauCoordinatesV1.wrapping_sub_natural _ _ (by decide)]
  rfl
theorem row_kind5 : rowOfKind 5#usize=3#usize := by
  unfold rowOfKind
  rw [if_neg (show ¬ (5#usize : Usize) < 4#usize from by decide)]
  apply UScalar.eq_of_val_eq
  rw [AspisR1S9ConstructorV3TauCoordinatesV1.wrapping_sub_natural _ _ (by decide)]
  rfl
theorem row_kind6 : rowOfKind 6#usize=4#usize := by
  unfold rowOfKind
  rw [if_neg (show ¬ (6#usize : Usize) < 4#usize from by decide)]
  apply UScalar.eq_of_val_eq
  rw [AspisR1S9ConstructorV3TauCoordinatesV1.wrapping_sub_natural _ _ (by decide)]
  rfl

#print axioms process_kind_success_reaches_tensor
#print axioms row_kind1
#print axioms row_kind2
#print axioms row_kind3
#print axioms row_kind5
#print axioms row_kind6
end AspisR1S9ActualProcessKindTensorReachedV1
