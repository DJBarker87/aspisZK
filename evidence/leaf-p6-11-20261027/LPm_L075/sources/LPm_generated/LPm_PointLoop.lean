import LPm_FinishPort
import LPm_PublicTwentyNine
import LPm_SemanticSelections
set_option autoImplicit false
namespace AspisR1.LPm_PointLoop
open Aeneas Aeneas.Std Result ControlFlow LPi_FieldValues LPm_RawPort
open AspisR1CurrentPreparedClaim
abbrev ops := AspisR1S5ClaimDotConcreteAdapter.concreteOps AspisR1EbyKPushDecodedProductUpdate.QRaw
abbrev Range := core.ops.range.Range Usize

/-- Linked local observations of the actual scalar loop. The read and weight
ports identify the caller's arguments; no loop Result or sum is assumed. -/
inductive Trace {H : Type} (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (g : Array Concrete.E 29#usize) (point : Usize) :
    Range → Native → List (NE×NQ) → NE → Prop where
  | done (iter iter' : Range) (s : Native) (out : NE)
      (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=ok (none,iter'))
      (finish : FIo_Native.fast_pairing.EbyKDot.finish s=ok out) :
      Trace sem y1 g point iter s [] out
  | step {iter iter' : Range} {s s' : Native} {out : NE} {xs : List (NE×NQ)}
      (l : Usize) (v : NE) (q : NQ)
      (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=ok (some l,iter'))
      (read : ClaimScalar.read ops sem y1 point l=ok (qPort q))
      (weight : Array.index_usize g l=ok (ePort v))
      (cv : canonE v) (cq : canonQ q) (count : s.count.val<29)
      (push : FIo_Native.fast_pairing.EbyKDot.push s v q=ok (.Ok (),s'))
      (tail : Trace sem y1 g point iter' s' xs out) :
      Trace sem y1 g point iter s ((v,q)::xs) out

theorem model_push (s s' : Native) (v : NE) (q : NQ)
    (cv : canonE v) (cq : canonQ q) (count : s.count.val<29)
    (push : FIo_Native.fast_pairing.EbyKDot.push s v q=ok (.Ok (),s')) :
    ops.pushDot (statePort s) (ePort v) (qPort q)=ok (.Ok (),statePort s') := by
  obtain ⟨actual,native,model⟩ := LPm_PublicPort.source s v q cv cq (by omega)
  have same : actual=s' := congrArg Prod.snd (Result.ok.inj (native.symm.trans push))
  subst actual
  exact model

theorem source {H : Type} (inst : aspis_core.Digest32 H)
    {sem : r1_semantic.Verified H} {y1 : Slice U8} {g : Array Concrete.E 29#usize}
    {point : Usize} {iter : Range} {s : Native} {xs : List (NE×NQ)} {out : NE}
    (tr : Trace sem y1 g point iter s xs out) :
    verifier.prepared_claim_dot_loop ops inst iter sem y1 g point (statePort s)=
      ok (.Ok (ePort out)) := by
  induction tr with
  | done iter iter' s out next finish =>
    obtain ⟨actual,native,model⟩ := LPm_FinishPort.source s
    have same := Result.ok.inj (native.symm.trans finish)
    subst actual
    have body : verifier.prepared_claim_dot_loop.body ops inst y1 g iter sem point (statePort s)=
        ok (ControlFlow.done (.Ok (ePort out))) := by
      rw [ClaimScalar.body_eq_source]
      simp only [ClaimScalar.body,next,bind_tc_ok,model]
    change Aeneas.Std.loop _ _ = _
    rw [Aeneas.Std.loop.eq_def]
    dsimp only
    rw [body]
    rfl
  | @step iter iter' s s' out xs l v q next read weight cv cq count push tail ih =>
    have model := model_push s s' v q cv cq count push
    have body : verifier.prepared_claim_dot_loop.body ops inst y1 g iter sem point (statePort s)=
        ok (ControlFlow.cont (iter',sem,point,statePort s')) := by
      rw [ClaimScalar.body_eq_source]
      simp only [ClaimScalar.body,next,bind_tc_ok,read,weight,model,
        core.result.Result.map_err,
        verifier.prepared_claim_dot.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError.call_once,
        core.result.Result.Insts.CoreOpsTry.branch]
    change Aeneas.Std.loop _ _ = _
    rw [Aeneas.Std.loop.eq_def]
    dsimp only
    rw [body]
    exact ih

#print axioms model_push
#print axioms source
end AspisR1.LPm_PointLoop
