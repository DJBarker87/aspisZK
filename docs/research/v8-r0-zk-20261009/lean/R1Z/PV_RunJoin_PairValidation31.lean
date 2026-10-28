import R1Z.PV_RunJoin_ZeroScan31
import R1Z.PV_RunJoin_Subtraction31
import R1Z.PV_RunJoin_PairChecks29
import AspisFormal.Pool.V7PairLeafOccupancy
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PairValidation31
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderAdmissionRanges
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {K : Type} [Field K] [CharP K 2147483647]

def model (p : pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1) : AspisPool.V7PairLeafOccupancy.PairLeaf K :=
  ⟨digK p.first_commitment,liftU p.second_occupied,digK p.second_commitment,liftU p.second_occupancy_inverse⟩

theorem word_equal (a b : U32)
    (h : core.cmp.PartialEq.ne.trait_default aspis_core.field.M31.Insts.CoreCmpPartialEqM31 a b = ok false) : a=b := by
  rw [PV_RunJoin_ForestEquality30.dictionary,PV_RunJoin_RuntimePrimitives30.word_ne] at h
  simpa only [Result.ok.injEq,decide_eq_false_iff_not,not_not] using h
#print axioms word_equal

theorem mul_meaning (a b z : U32) (h : aspis_core.field.M31.mul a b = ok z) :
    liftU (K := K) z = liftU a * liftU b := by
  obtain ⟨v,hv,_,hm⟩ := PV_Src_PortField.multiply (K := K) a b
  cases Result.ok.inj (hv.symm.trans h)
  exact hm
#print axioms mul_meaning

theorem sub_meaning (a b z : U32) (ha : a.val < 2147483647) (hb : b.val < 2147483647)
    (h : aspis_core.field.M31.sub a b = ok z) :
    liftU (K := K) z = liftU a - liftU b := by
  obtain ⟨v,hv,_,hm⟩ := PV_RunJoin_Subtraction31.field (K := K) a b ha hb
  cases Result.ok.inj (hv.symm.trans h)
  exact hm
#print axioms sub_meaning

theorem valid (p : pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1)
    (h : p.validate = ok (.Ok ())) : (model (K := K) p).Valid := by
  unfold pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.validate at h
  simp only [aspis_core.field.M31.ONE,aspis_core.field.M31.ZERO] at h
  pv_peel h with b hb
  obtain ⟨_,h⟩ := error_else h
  pv_peel h with b1 hb1
  obtain ⟨_,h⟩ := error_else h
  obtain ⟨ho,h⟩ := error_then h
  obtain ⟨hi,h⟩ := error_then h
  have hoc : p.second_occupied.val < 2147483647 := by
    simpa only [UScalar.le_equiv,aspis_core.field.P,UScalar.ofNatCore_val_eq,not_le] using ho
  have hic : p.second_occupancy_inverse.val < 2147483647 := by
    simpa only [UScalar.le_equiv,aspis_core.field.P,UScalar.ofNatCore_val_eq,not_le] using hi
  pv_peel h with om hom
  pv_peel h with mo hmo
  pv_peel h with m1 hm1
  pv_peel h with b2 hb2
  obtain ⟨hb2',h⟩ := error_then h
  have hb2f : b2=false := Bool.eq_false_iff.mpr hb2'
  subst b2
  simp only [Bool.false_eq_true,↓reduceIte] at h
  have he1 := word_equal _ _ hb2
  pv_peel h with sentinel hsentinel
  pv_peel h with m3 hm3
  pv_peel h with b3 hb3
  obtain ⟨hb3',h⟩ := error_then h
  have hb3f : b3=false := Bool.eq_false_iff.mpr hb3'
  subst b3
  simp only [Bool.false_eq_true,↓reduceIte] at h
  have he3 := word_equal _ _ hb3
  pv_peel h with m4 hm4
  pv_peel h with b4 hb4
  obtain ⟨hb4',h⟩ := error_then h
  have hb4f : b4=false := Bool.eq_false_iff.mpr hb4'
  subst b4
  simp only [Bool.false_eq_true,↓reduceIte] at h
  have he4 := word_equal _ _ hb4
  simp only [lift,bind_tc_ok,core.slice.Slice.iter] at h
  pv_peel h with scan hscan
  rcases scan with ⟨b5,after⟩
  obtain ⟨hb5',h⟩ := error_then h
  have hb5f : b5=false := Bool.eq_false_iff.mpr hb5'
  subst b5
  simp only [Bool.false_eq_true,↓reduceIte] at h
  have hs := PV_RunJoin_ZeroScan31.array (K := K) p.second_commitment om after hscan
  have homv := sub_meaning (K := K) _ _ _ (by decide) hoc hom
  have hmov := sub_meaning (K := K) _ _ _ hoc (by decide) hmo
  have hv1 := mul_meaning (K := K) _ _ _ hm1
  have hv3 := mul_meaning (K := K) _ _ _ hm3
  have hv4 := mul_meaning (K := K) _ _ _ hm4
  have hsent : sentinel = p.second_commitment.val[7]! := by
    rw [pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.second_sentinel,
      pool_v1.pair_tree_profile.POOL_V1_PAIR_SECOND_SENTINEL_LANE,
      index_ok p.second_commitment 7#usize (by decide)] at hsentinel
    exact (Result.ok.inj hsentinel).symm
  rw [he1] at hv1
  rw [he3,hsent] at hv3
  rw [he4] at hv4
  simp only [liftU,UScalar.ofNatCore_val_eq,Nat.cast_one,Nat.cast_zero] at homv hmov hv1 hv4
  change liftU (K := K) om = 1-liftU p.second_occupied at homv
  change liftU (K := K) mo = liftU p.second_occupied-1 at hmov
  change (0 : K) = liftU p.second_occupied * liftU mo at hv1
  change (0 : K) = liftU om * liftU p.second_occupancy_inverse at hv4
  refine ⟨?_,?_,?_,?_⟩
  · change liftU p.second_occupied * (liftU p.second_occupied-1)=0
    rw [← hmov]
    exact hv1.symm
  · exact hv3.symm
  · change (1-liftU p.second_occupied)*liftU p.second_occupancy_inverse=0
    rw [← homv]
    exact hv4.symm
  · intro j
    change (1-liftU p.second_occupied)*digK p.second_commitment j=0
    rw [← homv]
    exact hs j
#print axioms valid
end R1Z.PV_RunJoin_PairValidation31
