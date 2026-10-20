import CurrentClaimParserInstance
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1CurrentPreparedClaim.ClaimScalar
open Concrete
abbrev Range := core.ops.range.Range Usize

def read {D H : Type} (ops : ClaimDotOps D) (sem : r1_semantic.Verified H)
    (y1 : Slice U8) (point l : Usize) : Result aspis_core.field.QM31 := do
  if point ≤ 2#usize then
    let a ← Array.index_usize sem.claims point
    Array.index_usize a l
  else
    match point.val with
    | 3 => Array.index_usize sem.extra l
    | 4 => Array.index_usize sem.before_z1 l
    | _ => do
      let we ← ops.field y1 l
      ops.c0 we

def body {D H : Type} (ops : ClaimDotOps D) (inst : aspis_core.Digest32 H)
    (y1 : Slice U8) (g : Array E 29#usize) (iter : Range)
    (sem : r1_semantic.Verified H) (point : Usize) (dot : D) := do
  let (o,iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none =>
    let out ← ops.finishDot dot
    Result.ok (ControlFlow.done (α := Range × r1_semantic.Verified H × Usize × D) (core.result.Result.Ok out : core.result.Result E verifier.Error))
  | some l =>
    let scalar ← read ops sem y1 point l
    let coeff ← Array.index_usize g l
    let (r,dot1) ← ops.pushDot dot coeff scalar
    let r1 ← core.result.Result.map_err
      (verifier.prepared_claim_dot.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError inst) r ()
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ => Result.ok (ControlFlow.cont (iter1,sem,point,dot1))
    | core.ops.control_flow.ControlFlow.Break residual => do
      let r2 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        E (core.convert.FromSame verifier.Error) residual
      Result.ok (ControlFlow.done r2)

theorem body_eq_source {D H : Type} (ops : ClaimDotOps D) (inst : aspis_core.Digest32 H)
    (y1 : Slice U8) (g : Array E 29#usize) (iter : Range)
    (sem : r1_semantic.Verified H) (point : Usize) (dot : D) :
    verifier.prepared_claim_dot_loop.body ops inst y1 g iter sem point dot =
      body ops inst y1 g iter sem point dot := by
  have hzero : 0#usize ≤ point := by scalar_tac
  unfold verifier.prepared_claim_dot_loop.body body
  cases hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter with
  | fail e => simp only [bind_tc_fail]
  | div => simp only [bind_tc_div]
  | ok pair =>
    rcases pair with ⟨opt,iter1⟩
    cases opt with
    | none => rfl
    | some l =>
      simp only [bind_tc_ok,hzero,if_true,read]
      by_cases hsmall : point ≤ 2#usize
      · simp only [hsmall,if_true,bind_assoc_eq,bind_tc_ok]
        rfl
      · simp only [hsmall,if_false]
        split <;> simp_all only [bind_assoc_eq,bind_tc_ok] <;> rfl

#print axioms body_eq_source
end AspisR1CurrentPreparedClaim.ClaimScalar
