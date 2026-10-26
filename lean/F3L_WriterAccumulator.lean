import F3L_AccumulatorExt
import F3L_WriterNumeric
import CheckpointBytes5Writer
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_WriterAccumulator
open CheckpointBytes3Namespaces

theorem numeric (p : CheckpointBytes5Writer.Prepared) (a : AspisR1Stage2.verifier.Accumulator)
    (size : a.weights.val.length=64)
    (qb : ∀ j : Fin 22,(p.queries.val[j.val]'(by have h : p.queries.val.length=22:=p.queries.property;omega)).val<262144)
    (canonical : CheckpointBytesBlocks.CanonicalFields
      (CheckpointBytesBody.fields p (toAccumulator a) (by simpa only [toAccumulator,mapVec,List.length_map] using size) qb))
    (next : a.next.val=10) :
    CheckpointBytesBlocks.accumulator (CheckpointBytesBody.fields p (toAccumulator a)
      (by simpa only [toAccumulator,mapVec,List.length_map] using size) qb) canonical=
      CheckpointBytes5Output.accumulator a := by
  apply F3L_AccumulatorExt.fields
  · funext j
    have hj : j.val<a.weights.val.length := by rw [size];exact j.isLt
    change OraclePortCkptAbi5Codec.exactK _ (canonical.weights j)=_
    rw [F3L_WriterNumeric.exact_k]
    simp only [CheckpointBytesBody.fields,toAccumulator,mapVec,List.getElem_map,from_to_k,
      CheckpointBytes5Output.accumulator,List.getElem?_eq_getElem hj,Option.getD_some]
  · change OraclePortCkptAbi5Codec.exactE _ canonical.rhs=_
    rw [F3L_WriterNumeric.exact_e]
    exact congrArg CheckpointBytes5Output.ofE (from_to_e a.rhs)
  · change OraclePortCkptAbi5Codec.exactK _ canonical.power=_
    rw [F3L_WriterNumeric.exact_k]
    exact congrArg CheckpointBytes5Output.ofK (from_to_k a.power)
  · exact next.symm

#print axioms numeric
end AspisR1.F3L_WriterAccumulator
end
