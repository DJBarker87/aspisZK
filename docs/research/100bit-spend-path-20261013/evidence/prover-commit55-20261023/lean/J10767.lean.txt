import R1Z.ProverCommitOriginal55
import R1Z.ProverCommitConcreteMask51
import R1Z.ProverCommitExtraCaller51
import R1Z.ProverCommitSemanticRounds55
import R1Z.ProverCommitSemanticFinal55
import R1Z.ProverCommitEval50
/-! The actual final semantic comparison, with selected mask, coefficient
extra, two ordered additions and canonical raw equality. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitSemanticTerminal55
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
open ProverCommitTerminalZero55 (Statement publicModel)
open ProverCommitChallengePrefix55
open R0Z.HonestView R0Z.PayloadSplit R0Z.Shift R0Z.RefPayload
open ProverCommitInterpolationRow48
attribute [local instance] Classical.propDecidable
variable {Bat : Type} [BatchedLayer QM31Exact Bat]

def terminalMatch (out : Nat → Old.Q) (a mask original extra : Old.Q) : Result Bool := do
  let evaluated ← eval50.eval (ProverCommitEvalBlock50.source out) (ProverCommitNativeQ48.source a)
  let expected ← field.QM31.add (ProverCommitNativeQ48.source mask) (ProverCommitNativeQ48.source original)
  let expected ← field.QM31.add expected (ProverCommitNativeQ48.source extra)
  ok (decide (evaluated=expected))

def success (s : Statement) (sem : Nat → Old.Q) (c : Nat → Nat → Old.Q)
    (out : Nat → Old.Q) (original : Old.Q) : Prop :=
  ∃ mask extra : Old.Q,
    ProverCommitMaskRead51.run (ProverCommitQArray48.array 10#usize (ProverCommitOriginal55.point sem))
      (ProverCommitMaskColumns51.columns c) (ProverCommitQArray48.array 1024#usize (c 27))=
        ok (ProverCommitNativeQ48.source mask) ∧
    ProverCommitExtraCaller51.run (ProverCommitQArray48.array 1024#usize (c 28))
      (ProverCommitNativeQ48.source (sem 23)) (ProverCommitNativeQ48.source (sem 24))=
        ok (ProverCommitNativeQ48.source extra) ∧
    terminalMatch out (sem 24) mask original extra=ok true

attribute [local irreducible] ProverCommitQBasis51.basis publicModel ProverCommitClaims53.trace
  R0P.SemSource.honestClaims R0P.Mask.maskValue R0Z.PayloadSplit.maskLinear qpoly
  R0P.SemSource.terminalValue ProverCommitNativeQ48.source ProverCommitQArray48.array
  success terminalMatch shift refPayload L R0Z.Chain.roundPoly

theorem no_rejection (s : Statement) (sem : Nat → Old.Q)
    (hs : ∀ i, i<25 → Canonical (sem i))
    (c : Nat → Nat → Old.Q) (hc : ∀ l, l<29 → ∀ i, i<1024 → Canonical (c l i))
    (template : Challenges QM31Exact) (out : Nat → Old.Q) (hout : ∀ i, i<28 → Canonical (out i))
    (original : Old.Q) (ho : Canonical original)
    (hdo : decode original=fOrig (publicModel s) ProverCommitQBasis51.basis (withSemantic template sem)
      (ProverCommitClaims53.trace c) (alpha (withSemantic template sem)))
    (hpoly : qpoly out=R0Z.Chain.roundPoly 9 (shift (publicModel s) ProverCommitQBasis51.basis
      (withSemantic template sem) (refPayload (Bat := Bat) (publicModel s) ProverCommitQBasis51.basis
        (withSemantic template sem)+L AspisR1.rowEquiv ProverCommitQBasis51.basis
          (withSemantic template sem) (ProverCommitClaims53.trace c))))
    (hhalf : alpha (withSemantic template sem) 9≠1/2) : success s sem c out original := by
  let p := ProverCommitOriginal55.point sem
  have hp := ProverCommitOriginal55.point_canonical sem hs
  obtain ⟨mask,hm,hcm,hdm⟩ := ProverCommitConcreteMask51.exact_result p hp c hc
    (ProverCommitClaims53.trace c) (by intro l i;unfold ProverCommitClaims53.trace;rfl)
  obtain ⟨extra,he,hce,hde⟩ := ProverCommitExtraCaller51.exact_result (c 28) p
    (hc 28 (by decide)) hp (ProverCommitClaims53.trace c)
    (by intro i;unfold ProverCommitClaims53.trace;rfl)
  have hpoint : (fun i : Fin 10 => decode (p i.val))=alpha (withSemantic template sem) := rfl
  rw [hpoint] at hdm hde
  have hmask : decode mask+decode extra=maskLinear AspisR1.rowEquiv ProverCommitQBasis51.basis
      (alpha (withSemantic template sem)) (ProverCommitClaims53.trace c) := by
    rw [hdm,hde,maskLinear_apply]
  obtain ⟨expected1,h1,hc1,hd1⟩ := ProverCommitNativeQ48.add mask original hcm ho
  obtain ⟨expected,h2,hc2,hd2⟩ := ProverCommitNativeQ48.add expected1 extra hc1 hce
  obtain ⟨evaluated,hv,hcv,hdv⟩ := ProverCommitEval50.exact_result out (sem 24) hout (hs 24 (by decide))
  rw [ProverCommitSemanticFinal55.poly_eq_qpoly out,hpoly] at hdv
  have ha : decode (sem 24)=alpha (withSemantic template sem) 9 := rfl
  rw [ha,ProverCommitSemanticRounds55.shifted_terminal _ _ _ _ _ hhalf] at hdv
  have heq : evaluated=expected := by
    apply (AspisR1.ExtractedCurrentQM31Equality.decode_eq_iff _ _ hcv hc2).mp
    rw [hdv,hd2,hd1,←hmask,hdo]
    ring
  unfold success
  refine ⟨mask,extra,hm,he,?_⟩
  rw [terminalMatch,hv,h1]
  simp only [bind_tc_ok,h2,heq,decide_true]

#print axioms no_rejection
end R1Z.ProverCommitSemanticTerminal55
