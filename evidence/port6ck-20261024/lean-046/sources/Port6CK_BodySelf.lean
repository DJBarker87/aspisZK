import Port6CK_ArrayRoundtrip
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6CK_BodySelf
open Aeneas Aeneas.Std AspisR1Stage2
open CheckpointBytes4SavedFields CheckpointBytes4ReaderFields
open CheckpointBytes3Namespaces Port3_DecodeCoherence
open Port6CK_ScalarRoundtrip

theorem fields (p : verifier.Prepared) (a : verifier.Accumulator)
    (variant : p.variant=.S2) (size : a.weights.val.length=64)
    (qb : ∀ j : Fin 22, (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val<262144)
    (canonical : CheckpointBytesBlocks.CanonicalFields (inventory p a size qb)) :
    BodyMatches p a (CheckpointBytesBlocks.prepared (inventory p a size qb) canonical)
      (CheckpointBytesBlocks.accumulator (inventory p a size qb) canonical) := by
  refine ⟨variant,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (CheckpointBytesDigest.bytes_stateOf p.state).symm
  · obtain ⟨x,y,h⟩ := List.length_eq_two.mp p.roots.property
    change p.roots.val.map (fun b : Array U8 32#usize => MultiproofConeCanonical.bytesOf b.val) =
      [_,_]
    dsimp only [inventory,CheckpointBytesBlocks.prepared,CheckpointBytesBody.fields,toPrepared]
    rw [CheckpointBytesDigest.bytes_stateOf,CheckpointBytesDigest.bytes_stateOf]
    rw [h]
    rfl
  · exact (e p.gamma canonical.gamma).symm
  · exact (e p.kappa canonical.kappa).symm
  · obtain ⟨x,y,h⟩ := List.length_eq_two.mp p.alpha.property
    change p.alpha.val = [sourceE (OraclePortCkptAbi5Codec.exactE _ _),sourceE (OraclePortCkptAbi5Codec.exactE _ _)]
    rw [show sourceE (OraclePortCkptAbi5Codec.exactE _ _)=p.alpha.val[0]'(by simp [p.alpha.property]) from e _ (canonical.alpha 0)]
    rw [show sourceE (OraclePortCkptAbi5Codec.exactE _ _)=p.alpha.val[1]'(by simp [p.alpha.property]) from e _ (canonical.alpha 1)]
    rw [h]
    rfl
  · exact (k p.rho canonical.rho).symm
  · apply List.ext_getElem
    · simp only [List.length_map,List.length_ofFn,p.queries.property]; rfl
    · intro i hi hj
      simp only [List.getElem_map,List.getElem_ofFn]
      rfl
  · have canon : ∀ j : Fin 10, OraclePortCkptAbi4Decode.Canonical
        (toK (p.semantic_alpha.val[j.val]'(by have len : p.semantic_alpha.val.length=10 := p.semantic_alpha.property; rw [len]; exact j.isLt))) := by
      intro j
      simpa only [inventory,CheckpointBytesBody.fields,toPrepared,mapArray,List.getElem_map] using canonical.semanticAlpha j
    simpa only [inventory,CheckpointBytesBlocks.prepared,CheckpointBytesBody.fields,toPrepared,mapArray,List.getElem_map]
      using Port6CK_ArrayRoundtrip.k p.semantic_alpha.val 10 p.semantic_alpha.property canon
  · obtain ⟨x,y,h⟩ := List.length_eq_two.mp p.z.property
    have each : ∀ j : Fin 4, sourceK ((CheckpointBytesBlocks.prepared (inventory p a size qb) canonical).coordinates j)=
        match j.val with
        | 0 => (p.z.val[0]'(by simp [p.z.property])).x
        | 1 => (p.z.val[0]'(by simp [p.z.property])).y
        | 2 => (p.z.val[1]'(by simp [p.z.property])).x
        | _ => (p.z.val[1]'(by simp [p.z.property])).y := by
      intro j
      have raw := canonical.coordinates j
      simp only [inventory,CheckpointBytesBody.fields,toPrepared,mapArray,List.getElem_map,toPoint] at raw
      simp only [CheckpointBytesBlocks.prepared,inventory,CheckpointBytesBody.fields,toPrepared,mapArray,List.getElem_map,toPoint]
      fin_cases j
      all_goals exact k _ raw
    rw [List.map_ofFn]
    simp_rw [each]
    rw [h]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.cons_append]
    rfl
  · exact (e p.claim canonical.claim).symm
  · exact (e a.rhs canonical.rhs).symm
  · exact (k a.power canonical.power).symm
  · have canon : ∀ j : Fin 64, OraclePortCkptAbi4Decode.Canonical
        (toK (a.weights.val[j.val]'(by omega))) := by
      intro j
      simpa only [inventory,CheckpointBytesBody.fields,toAccumulator,mapVec,List.getElem_map] using canonical.weights j
    simpa only [inventory,CheckpointBytesBlocks.accumulator,CheckpointBytesBody.fields,toAccumulator,mapVec,List.getElem_map]
      using Port6CK_ArrayRoundtrip.k a.weights.val 64 size canon

#print axioms fields
end AspisR1.Port6CK_BodySelf
end
