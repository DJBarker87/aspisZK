import R1Z.PV_Src_AdmissionScalar
import R1Z.PV_Src_AdmissionDigest

/-! Empty-side constraints vanish for an occupied pair; the source iterator
still executes with its original short-circuit state. -/
set_option autoImplicit false
namespace R1Z.PV_Src_AdmissionOccupiedScan
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open AspisBuilderAdmissionSource BuilderAdmissionStd

theorem scan_false (d : Array U32 8#usize) : ∃ after,
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any
      pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.validate.closure.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool
      ⟨Array.to_slice d,0⟩ 0#u32 = ok (false,after) := by
  let f := pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.validate.closure.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool
  have hf : ∀ (c : U32) (x : U32), c = 0#u32 → f.call_mut c x = ok (false,c) := by
    intro c x hc
    subst c
    change (do
      let m ← aspis_core.field.M31.mul 0#u32 x
      let b ← core.cmp.PartialEq.ne.trait_default aspis_core.field.M31.Insts.CoreCmpPartialEqM31 m aspis_core.field.M31.ZERO
      ok (b,0#u32)) = _
    rw [PV_Src_AdmissionScalar.mul_zero]
    simp [bind_tc_ok,aspis_core.field.M31.ZERO,
      core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
      aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq]
  have hs : ∀ (xs : List U32), scan f true xs 0#u32 = ok (false,xs.length) := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih => rw [scan,hf _ _ rfl];simp only [bind_tc_ok]; rw [ih];rfl
  refine ⟨⟨Array.to_slice d,d.val.length⟩,?_⟩
  change iterScan f true ⟨Array.to_slice d,0⟩ 0#u32 = _
  unfold iterScan
  simp only [Array.to_slice,List.drop_zero]
  rw [hs]
  simp only [bind_tc_ok,Nat.zero_add]

#print axioms scan_false
end R1Z.PV_Src_AdmissionOccupiedScan
