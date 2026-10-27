import JFn_ValueBlock
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_ArrayBuilder
open Aeneas Aeneas.Std Result
open AspisR1Stage2 Port3_NativeQueryBody

def ops (seed : Port3_NativeQueryBody.Ops) : Port3_NativeQueryBody.Ops :=
  Port4C_RowStd.install (Port5Q1_QueryPorts.install (SAQ_Decoder.install seed))

/-- The four real source decoder closures execute in increasing index
order. No returned array or successful builder call is assumed. -/
theorem source (seed : Port3_NativeQueryBody.Ops) (i : Fin 22)
    (a b c d : SAQ_WideABI.E)
    (h0 : SAQ_Decoder.read (JFn_ValueBlock.value i) 0#usize=ok a)
    (h1 : SAQ_Decoder.read (JFn_ValueBlock.value i) 1#usize=ok b)
    (h2 : SAQ_Decoder.read (JFn_ValueBlock.value i) 2#usize=ok c)
    (h3 : SAQ_Decoder.read (JFn_ValueBlock.value i) 3#usize=ok d) :
    (ops seed).op0 4#usize
      (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (ops seed))
      (JFo_Opening.value i)=ok (Array.make 4#usize [a,b,c,d]) := by
  have c0:=JFn_ValueBlock.closure seed i 0#usize a h0
  have c1:=JFn_ValueBlock.closure seed i 1#usize b h1
  have c2:=JFn_ValueBlock.closure seed i 2#usize c h2
  have c3:=JFn_ValueBlock.closure seed i 3#usize d h3
  change OraclePortStdBuilder.fromFn 4#usize _ _=ok _
  unfold OraclePortStdBuilder.fromFn
  rw [Port4C_QueryStd.indices_four]
  simp only [OraclePortStdBuilder.fromFnLoop,
    verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact,
    ops,c0,c1,c2,c3,bind_tc_ok]
  rfl

#print axioms source
end AspisR1.JFn_ArrayBuilder
end
