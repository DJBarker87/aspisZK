import R1Z.PV_RunJoin_ExternalLanes
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ExternalRefinement
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
variable {K : Type} [Field K] [CharP K 2147483647]

/-- Complete owned external-layer source refinement, including totality,
canonical raw output and the field-model equation. Every input word is raw
U32; there is no successful-execution or canonicality hypothesis. The pinned
native source/owned equality remains the sibling's separate Kani evidence. -/
theorem owned (state : Array U32 16#usize) :
    ∃ out, PV_Src_ExternalReference.run state = ok out ∧
      (∀ j, j < 16 → out.val[j]!.val < 2147483647) ∧
      ∀ i : Fin 16, liftU (K := K) out.val[i.val]! =
        R0P.poseidonExternalLinear (liftA state) i := by
  obtain ⟨grouped,hgrouped,hG⟩ := PV_RunJoin_ExternalBlocksCopy.field_entry (K := K) state
  refine ⟨PV_RunJoin_ExternalLanes.target grouped,?_,PV_RunJoin_ExternalLanes.canonical grouped,?_⟩
  · rw [PV_Src_ExternalReference.run,
      AspisBuilderPoseidonReference.poseidon2.builder_reference.external_owned,hgrouped]
    simp only [bind_tc_ok]
    rw [PV_RunJoin_ExternalSums.entry]
    simp only [bind_tc_ok]
    exact PV_RunJoin_ExternalLanes.entry grouped
  · intro i
    have hi := i.isLt
    rw [PV_RunJoin_ExternalLanes.field_value grouped i.val hi,
      PV_RunJoin_ExternalSums.field_value grouped ⟨i.val%4,by omega⟩,ext_unfold]
    have G := hG ⟨i.val/4,by omega⟩ ⟨i.val%4,by omega⟩
    have G0 := hG 0 ⟨i.val%4,by omega⟩
    have G1 := hG 1 ⟨i.val%4,by omega⟩
    have G2 := hG 2 ⟨i.val%4,by omega⟩
    have G3 := hG 3 ⟨i.val%4,by omega⟩
    change liftU (K := K) grouped.val[4*0+i.val%4]! = PM state ⟨0,by decide⟩ ⟨i.val%4,by omega⟩ at G0
    change liftU (K := K) grouped.val[4*1+i.val%4]! = PM state ⟨1,by decide⟩ ⟨i.val%4,by omega⟩ at G1
    change liftU (K := K) grouped.val[4*2+i.val%4]! = PM state ⟨2,by decide⟩ ⟨i.val%4,by omega⟩ at G2
    change liftU (K := K) grouped.val[4*3+i.val%4]! = PM state ⟨3,by decide⟩ ⟨i.val%4,by omega⟩ at G3
    rw [Nat.div_add_mod] at G
    rw [show 4*0+i.val%4 = i.val%4 by omega] at G0
    rw [show 4*1+i.val%4 = i.val%4+4 by omega] at G1
    rw [show 4*2+i.val%4 = i.val%4+8 by omega] at G2
    rw [show 4*3+i.val%4 = i.val%4+12 by omega] at G3
    unfold liftN
    rw [←G,←G0,←G1,←G2,←G3]
    ring

/-- The SAME source dictionary consumed by FrozenInput's actual forest
extraction inherits the whole-layer theorem; no new callback premise appears. -/
theorem dictionary (state : Array U32 16#usize) :
    ∃ out,
      @BuilderForestAdmissionPort.poseidon2.external_linear_lazy PV_Src_ExternalReference.dictionary state = ok out ∧
      (∀ j, j < 16 → out.val[j]!.val < 2147483647) ∧
      ∀ i : Fin 16, liftU (K := K) out.val[i.val]! =
        R0P.poseidonExternalLinear (liftA state) i := by
  obtain ⟨out,run,canonical,meaning⟩ := owned (K := K) state
  exact ⟨out,(PV_Src_ExternalReference.call_eq state).trans run,canonical,meaning⟩

#print axioms owned
#print axioms dictionary
end R1Z.PV_RunJoin_ExternalRefinement
