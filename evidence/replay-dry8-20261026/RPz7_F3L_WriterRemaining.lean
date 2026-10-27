import RPz7_F3L_SourcePrepared
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_WriterRemaining
open AspisR1PublicPreparation
open F3K_CheckpointPreparedFields

theorem fields (out : verifier.Prepared) (a : CheckpointBytes5Writer.Accumulator)
    (size : a.weights.val.length=64)
    (qb : ∀ j : Fin 22,((writerPrepared out).queries.val[j.val]'(by have h : (writerPrepared out).queries.val.length=22 := (writerPrepared out).queries.property;omega)).val<262144)
    (canonical : CheckpointBytesBlocks.CanonicalFields (CheckpointBytesBody.fields (writerPrepared out) a size qb)) :
    let pm := CheckpointBytesBlocks.prepared (CheckpointBytesBody.fields (writerPrepared out) a size qb) canonical
    pm.roots=(F3L_SourcePrepared.numeric out).roots ∧
    pm.queries=(F3L_SourcePrepared.numeric out).queries ∧
    pm.claim=(F3L_SourcePrepared.numeric out).claim := by
  refine ⟨rfl,?_,?_⟩
  · funext j
    apply Fin.ext
    have hj : j.val<out.queries.val.length := by have h : out.queries.val.length=22:=out.queries.property;omega
    change (out.queries.val[j.val]'hj).val=
      ((out.queries.val.map (fun x=>x.val))[j.val]?.getD 0)%262144
    rw [List.getElem?_map,List.getElem?_eq_getElem hj]
    simp only [Option.map_some,Option.getD_some]
    exact (Nat.mod_eq_of_lt (qb j)).symm
  · exact F3L_WriterSourceScalar.exact_e out.claim canonical.claim

#print axioms fields
end AspisR1.F3L_WriterRemaining
end
