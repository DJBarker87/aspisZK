import TxS_Writer
set_option autoImplicit false
noncomputable section
namespace AspisR1.TxS_Prepared
open Aeneas Aeneas.Std Result AspisR1Stage2 CheckpointBytes3Namespaces

/-- Only the fields read by the query loop; the complete encoding remains in Writer.saved. -/
theorem fields (p : verifier.Prepared) (a : verifier.Accumulator)
    (size : a.weights.val.length=64)
    (qb : ∀ j : Fin 22,(p.queries.val[j.val]'(by have h : p.queries.val.length=22:=p.queries.property;omega)).val<262144)
    (canonical : CheckpointBytesBlocks.CanonicalFields (Port3_DecodeCoherence.inventory p a size qb)) :
    let pm := CheckpointBytesBlocks.prepared (Port3_DecodeCoherence.inventory p a size qb) canonical
    pm.rho=CheckpointBytes5Output.ofK p.rho ∧
    pm.queries=CheckpointBytes5Output.queries p ∧
    ∀ j : Fin 2, pm.alpha j=CheckpointBytes5Output.ofE
      (p.alpha.val[j.val]'(by have h : p.alpha.val.length=2:=p.alpha.property;omega)) := by
  refine ⟨Port3_DecodeCoherence.k_decode _ canonical.rho,?_,?_⟩
  · funext j
    apply Fin.ext
    have hj : j.val<p.queries.val.length := by have h : p.queries.val.length=22:=p.queries.property;omega
    simp only [CheckpointBytesBlocks.prepared,Port3_DecodeCoherence.inventory,CheckpointBytesBody.fields,
      toPrepared,CheckpointBytes5Output.queries,List.getElem?_map,List.getElem?_eq_getElem hj,
      Option.map_some,Option.getD_some]
    exact (Nat.mod_eq_of_lt (qb j)).symm
  · intro j
    change OraclePortCkptAbi5Codec.exactE _ (canonical.alpha j)=_
    have hc : OraclePortCkptAbi4Decode.CanonicalWide (toE (p.alpha.val[j.val]'_)) := by
      simpa only [Port3_DecodeCoherence.inventory,CheckpointBytesBody.fields,toPrepared,mapArray,List.getElem_map] using canonical.alpha j
    simpa only [Port3_DecodeCoherence.inventory,CheckpointBytesBody.fields,toPrepared,mapArray,List.getElem_map]
      using Port3_DecodeCoherence.e_decode (p.alpha.val[j.val]'_) hc

#print axioms fields
end AspisR1.TxS_Prepared
end
