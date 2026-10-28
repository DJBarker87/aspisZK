import NDO_JGi_TX1Prefix
set_option autoImplicit false
namespace AspisR1.JGi_TX1Control
open Aeneas Aeneas.Std Result AspisR1CurrentCaller

def afterScan {H : Type} (ops : Ops) (D : aspis_core.digest.Digest32 H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (hash : H) : Result (core.result.Result (alloc.vec.Vec U8) verifier.Error) := do
  let zero ← aspis_core.field.wide_exact.WideExact.ZERO ops
  let (r,scratch) ← verifier.candidate.prepare ops D semantic proof hash none (Array.repeat 29#usize zero)
  match r with
  | .Ok p => Tx1Reachability.afterPrepare ops D pub proof 10#usize hash none p scratch
  | .Err e => ok (.Err e)

theorem source {H : Type} (ops : Ops) (D : aspis_core.digest.Digest32 H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (hash : H)
    (shape : ops.op3 proof=ok (.Ok .S2)) (scan : ops.op4 proof=ok (.Ok ())) :
    verifier.candidate.tx1 ops D semantic pub proof 10#usize hash none=afterScan ops D semantic pub proof hash := by
  unfold verifier.candidate.tx1 afterScan
  simp only [compact.SPLIT,show (10#usize != 10#usize)=false from rfl,Bool.false_eq_true,if_false,
    shape,scan,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,verifier.mark]
  apply bind_congr
  intro zero
  apply bind_congr
  rintro ⟨r,scratch⟩
  cases r with
  | Err e => rfl
  | Ok p => rfl
#print axioms source
end AspisR1.JGi_TX1Control
