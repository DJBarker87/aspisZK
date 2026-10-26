import ARQ_FirstTrace
import Port1_Driver
set_option autoImplicit false
namespace AspisR1.ARQ_CallFacts
open Aeneas Aeneas.Std Result

theorem decoded (ops : AdapterRw.Ops) (pub : Slice U8)
    (statement : AdapterRw.Cuts.Statement) (semantic : Port1_Driver.Semantic)
    (decode : S2W_Trace.invoke ops (.op47 pub) = ok (.Ok statement))
    (validate : S2W_Trace.invoke ops (.op21 statement) = ok (.Ok ()))
    (getter : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
      statement = ok semantic) :
    Port1_Driver.decodeSemantic ops pub = ok (some semantic) := by
  change ops.op47 pub = _ at decode
  change ops.op21 statement = _ at validate
  simp only [Port1_Driver.decodeSemantic,decode,validate,getter,bind_tc_ok]

theorem first (ops : AdapterRw.Ops) (semantic : Port1_Driver.Semantic)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (called : S2W_Trace.invoke ops
      (.op10 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
        semantic pub proof split () none) = ok (.Ok saved)) :
    AdapterRw.first_decoded ops semantic pub proof split = ok (.Ok saved) := by
  change ops.op10 _ _ _ _ _ _ _ = _ at called
  simp only [AdapterRw.first_decoded,AdapterRw.observer,called,bind_tc_ok,core.result.Result.map_err]

#print axioms decoded
#print axioms first
end AspisR1.ARQ_CallFacts
