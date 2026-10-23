import R1Z.ProverCommitTerminalZero55
import R1Z.ProverCommitConcreteMask51
import R1Z.ProverCommitExtraCaller51
import R1Z.ProverCommitClaims53
import R1Z.ProverCommitSemanticModel55
import R1Z.ProverCommitChallengePrefix55
/-! Complete owned semantic sample function: selected mask, coefficient extra,
actual retained zero-claim terminal, eta multiplication and both additions.
The retained terminal's public-preparation/source binding remains explicit. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitOracle55
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
open ProverCommitTerminalZero55 (Statement publicModel)
open ProverCommitSuccessorPoint49 (decoded)

def run (s : Statement) (sem p : Nat → Old.Q) (c : Nat → Nat → Old.Q) :
    Result (core.result.Result field.QM31 AspisR1.CompositionPartsTail.Error) := do
  let mask ← ProverCommitMaskRead51.run (ProverCommitQArray48.array 10#usize p)
    (ProverCommitMaskColumns51.columns c) (ProverCommitQArray48.array 1024#usize (c 27))
  let extra ← ProverCommitExtraCaller51.run (ProverCommitQArray48.array 1024#usize (c 28))
    (ProverCommitNativeQ48.source (p 8)) (ProverCommitNativeQ48.source (p 9))
  let combined ← field.QM31.add mask extra
  let terminal ← ProverCommitTerminalZero55.run s sem p
  match terminal with
  | .Err error => ok (.Err error)
  | .Ok (terminal,_,_,_) => do
    let prod ← field.QM31.mul (ProverCommitNativeQ48.source (sem 14))
      (ProverCommitNativeQ48.source (ProverCommitTerminalCarrier55.fromSelected terminal))
    let out ← field.QM31.add combined prod
    ok (.Ok out)

theorem zero_claims (p : Fin 10 → QM31Exact) :
    R0P.SemSource.honestClaims (0 : R0P.Trace QM31Exact) p=fun _ _ => 0 := by
  funext r l
  simp only [R0P.SemSource.honestClaims,AspisR0.LinearDual.dot,
    Pi.zero_apply,mul_zero,Finset.sum_const_zero]

attribute [local irreducible] R0P.SemSource.honestClaims R0Z.PayloadSplit.maskLinear
  R0P.Mask.maskValue ProverCommitQBasis51.basis ProverCommitClaims53.trace
  ProverCommitTerminalZero55.publicModel R0P.SemSource.terminalValue

theorem exact_result (s : Statement) (sem p : Nat → Old.Q)
    (hs : ∀ i, i<25 → Canonical (sem i)) (hp : ∀ i, i<10 → Canonical (p i))
    (c : Nat → Nat → Old.Q) (hc : ∀ l, l<29 → ∀ i, i<1024 → Canonical (c l i))
    (template : R0Z.HonestView.Challenges QM31Exact)
    {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (hash : H) (c1 : Array U8 32#usize)
    (transcript : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (hprep : AspisR1PublicPreparation.r1_semantic.public_transcript D
      (AspisR1PublicPreparation.PreparationBinding.preparationPublic s) hash c1=ok (.Ok transcript)) :
    ∃ out : Old.Q, run s sem p c=ok (.Ok (ProverCommitNativeQ48.source out)) ∧ Canonical out ∧
      decode out=ProverCommitSemanticModel55.oracle AspisR1.rowEquiv (publicModel s)
        ProverCommitQBasis51.basis (ProverCommitChallengePrefix55.withSemantic template sem)
        (ProverCommitClaims53.trace c) (decoded p) := by
  obtain ⟨mask,hmask,hcmask,hdmask⟩ := ProverCommitConcreteMask51.exact_result p hp c hc
    (ProverCommitClaims53.trace c) (by intro l i;unfold ProverCommitClaims53.trace;rfl)
  obtain ⟨extra,hextra,hcextra,hdextra⟩ := ProverCommitExtraCaller51.exact_result (c 28) p
    (hc 28 (by decide)) hp (ProverCommitClaims53.trace c) (by intro i;unfold ProverCommitClaims53.trace;rfl)
  obtain ⟨combined,hcombined,hccombined,hdcombined⟩ := ProverCommitNativeQ48.add mask extra hcmask hcextra
  obtain ⟨z,mo,g,terminal,hterminal,hcterminal,hdterminal⟩ :=
    ProverCommitTerminalZero55.exact_result s sem p hs hp D hash c1 transcript hprep
  obtain ⟨prod,hprod,hcprod,hdprod⟩ := ProverCommitNativeQ48.mul (sem 14)
    (ProverCommitTerminalCarrier55.fromSelected terminal) (hs 14 (by decide)) hcterminal
  obtain ⟨out,hout,hcout,hdout⟩ := ProverCommitNativeQ48.add combined prod hccombined hcprod
  refine ⟨out,?_,hcout,?_⟩
  · simp only [run,hmask,hextra,hcombined,hterminal,hprod,hout,bind_tc_ok]
  · have hdecoded : (fun i : Fin 10 => decode (p i.val))=decoded p := rfl
    rw [hdecoded] at hdmask hdextra
    have hmasklinear : decode mask+decode extra=R0Z.PayloadSplit.maskLinear AspisR1.rowEquiv
        ProverCommitQBasis51.basis (decoded p) (ProverCommitClaims53.trace c) := by
      rw [hdmask,hdextra,R0Z.PayloadSplit.maskLinear_apply]
    rw [hdout,hdcombined,hdprod,hmasklinear,hdterminal]
    have hzc : R0Z.HonestView.zc (ProverCommitChallengePrefix55.withSemantic template sem)=
        (fun i : Fin 10 => decode (sem (3+i.val))) := rfl
    simp only [ProverCommitSemanticModel55.oracle,R0Z.Shift.fOrig,zero_claims]
    rw [hzc]
    rfl

#print axioms zero_claims
#print axioms exact_result
end R1Z.ProverCommitOracle55
