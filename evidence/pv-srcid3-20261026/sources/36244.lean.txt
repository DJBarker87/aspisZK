import R1Z.PV_Src_AdmissionOccupiedScan

/-! Source pair validation for the fixture's occupied first/second layout.
The inverse equation is primitive arithmetic, discharged by field transport
in the following module. -/
set_option autoImplicit false
namespace R1Z.PV_Src_AdmissionOccupied
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open AspisBuilderAdmissionSource

def pair (first second : Array U32 8#usize) (inverse : U32) :
    pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1 := ⟨first,1#u32,second,inverse⟩

theorem validates (first second : Array U32 8#usize) (inverse : U32)
    (hf : Canon8 first) (hs : Canon8 second) (hi : inverse.val < 2147483647)
    (hne : second.val[7]! ≠ 0#u32)
    (hm : aspis_core.field.M31.mul second.val[7]! inverse = ok 1#u32) :
    (pair first second inverse).validate = ok (.Ok ()) := by
  rw [pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.validate]
  dsimp only [pair]
  rw [PV_Src_AdmissionDigest.tree_true _ hf]
  simp only [bind_tc_ok,↓reduceIte]
  rw [PV_Src_AdmissionDigest.tree_true _ hs]
  simp only [bind_tc_ok,↓reduceIte,pair,aspis_core.field.P,
    aspis_core.field.M31.ONE,aspis_core.field.M31.ZERO]
  rw [if_neg (by decide : ¬(1#u32 : U32) ≥ 2147483647#u32)]
  rw [if_neg (by simpa only [UScalar.le_equiv,UScalar.ofNatCore_val_eq] using Nat.not_le.mpr hi)]
  rw [PV_Src_AdmissionScalar.sub_self _ (by decide)]
  simp only [bind_tc_ok]
  have mul10 : aspis_core.field.M31.mul 1#u32 0#u32 = ok 0#u32 := by
    have comm : U64.wrapping_mul (UScalar.cast .U64 (1#u32 : U32)) (UScalar.cast .U64 (0#u32 : U32)) =
        U64.wrapping_mul (UScalar.cast .U64 (0#u32 : U32)) (UScalar.cast .U64 (1#u32 : U32)) := by
      apply UScalar.eq_of_val_eq
      simp only [U64.wrapping_mul_val_eq,Nat.mul_comm]
    simpa only [aspis_core.field.M31.mul,lift,bind_tc_ok,comm] using
      (PV_Src_AdmissionScalar.mul_zero 1#u32)
  rw [mul10]
  simp [bind_tc_ok,core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
    aspis_core.field.M31.Insts.CoreCmpPartialEqM31,
    aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq,↓reduceIte]
  rw [pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.second_sentinel,
    pool_v1.pair_tree_profile.POOL_V1_PAIR_SECOND_SENTINEL_LANE]
  rw [index_ok second 7#usize (by decide)]
  simp only [bind_tc_ok,UScalar.ofNatCore_val_eq]
  change (do
    let m3 ← aspis_core.field.M31.mul second.val[7]! inverse
    _) = _
  rw [hm,PV_Src_AdmissionScalar.mul_zero]
  simp [bind_tc_ok,core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
    aspis_core.field.M31.Insts.CoreCmpPartialEqM31,
    aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq,↓reduceIte]
  obtain ⟨after,hscan⟩ := PV_Src_AdmissionOccupiedScan.scan_false second
  simp only [lift,bind_tc_ok,core.slice.Slice.iter]
  rw [hscan]
  simp [bind_tc_ok,aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq,hne]
  simpa using hne

#print axioms validates
end R1Z.PV_Src_AdmissionOccupied
