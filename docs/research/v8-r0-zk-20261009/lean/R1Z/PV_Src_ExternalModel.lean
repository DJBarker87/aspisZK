import R1Z.PV_Src_ExternalGroupsModel
import R1Z.PV_Src_ExternalSumModel
import R1Z.PV_Src_ExternalLaneModel

/-! The owned external layer implements the frozen field-model map on every
U32 state. This statement identifies the owned source, not an installed callback. -/
set_option autoImplicit false
namespace R1Z.PV_Src_ExternalModel
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open AspisBuilderPoseidonReference

theorem source (s : Array U32 16#usize)
    {K : Type} [Field K] [CharP K 2147483647] : ∃ out,
    PV_Src_ExternalReference.run s = ok out ∧
    (∀ j : Fin 16, out.val[j.val]!.val < 2147483647) ∧
    ∀ j : Fin 16, liftU (K := K) out.val[j.val]! =
      R0P.poseidonExternalLinear (liftA s) j := by
  obtain ⟨gr,hgr,hG⟩ := PV_Src_ExternalGroupsModel.source (K := K) s
  obtain ⟨sums,hsums,hS⟩ := PV_Src_ExternalSumModel.total gr
  obtain ⟨out,hout,hcan,hT⟩ := PV_Src_ExternalLaneModel.model (K := K) gr sums
    (PV_Src_ExternalSumModel.bound gr sums hS)
  refine ⟨out,?_,hcan,?_⟩
  · rw [PV_Src_ExternalReference.run,poseidon2.builder_reference.external_owned,hgr]
    simp only [bind_tc_ok]
    rw [hsums]
    simpa only [bind_tc_ok] using hout
  · intro i
    rw [hT i,hS ⟨i.val%4,Nat.mod_lt _ (by decide)⟩,
      PV_Src_ExternalSumValue.lift,ext_unfold]
    have G := hG (i.val/4) (i.val%4) (by have := i.isLt;omega) (by omega)
    have G0 := hG 0 (i.val%4) (by decide) (by omega)
    have G1 := hG 1 (i.val%4) (by decide) (by omega)
    have G2 := hG 2 (i.val%4) (by decide) (by omega)
    have G3 := hG 3 (i.val%4) (by decide) (by omega)
    rw [Nat.div_add_mod] at G
    rw [show 4*0+i.val%4=i.val%4 by omega] at G0
    rw [show 4*1+i.val%4=4+i.val%4 by omega] at G1
    rw [show 4*2+i.val%4=8+i.val%4 by omega] at G2
    rw [show 4*3+i.val%4=12+i.val%4 by omega] at G3
    simp only [UScalar.ofNatCore_val_eq]
    rw [← G,← G0,← G1,← G2,← G3]
    have hv : (Usize.ofNatCore (i.val%4) (by have hm := Nat.mod_lt i.val (show 0<4 by decide);scalar_tac)).val = i.val%4 := by
      scalar_tac
    simp only [liftN,hv,Nat.add_comm]
    ring

#print axioms source
end R1Z.PV_Src_ExternalModel
