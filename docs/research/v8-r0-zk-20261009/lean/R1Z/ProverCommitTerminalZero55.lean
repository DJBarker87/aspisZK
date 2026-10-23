import R1Z.ProverCommitTerminalCarrier55
import R1Z.ProverCommitSubfieldOps47
/-! Construct the actual zero-claim terminal invocation used by every semantic
sample. Only public preparation and canonical caller inputs remain premises. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitTerminalZero55
open Aeneas Aeneas.Std Result
open ProverCommitPrimitive47 ProverCommitSubfieldOps47 ProverCommitTerminalCarrier55
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
open AspisR1TerminalDigestBindingCandidate.SemanticPublicPreparationCopy
abbrev Statement := AspisR1TerminalDecoder.PublicBinding.Statement

def publicModel (s : Statement) := AspisR1.SemanticCompositionCoefficients.exactPublic (copyFromStatement s)
def zeroClaims := array 84#usize (fun _ => zero)
def zc (sem : Nat → Old.Q) := array 10#usize (fun i => sem (3+i))
def run (s : Statement) (sem p : Nat → Old.Q) :=
  ProverCommitTerminalQName55.run (copyFromStatement s) zeroClaims (array 10#usize p)
    (toSelected (sem 0)) (toSelected (sem 1)) (toSelected (sem 2)) (zc sem) (toSelected (sem 13))

theorem claims_zero : AspisR1.TerminalClaimModel53.claims zeroClaims=fun _ _ => (0 : QM31Exact) := by
  funext r c
  unfold AspisR1.TerminalClaimModel53.claims
  split
  · simp only [zeroClaims,array,ProverCommitArray49.array,List.getElem_ofFn,decode_to,zero_decode]
  · rfl

theorem exact_result (s : Statement) (sem p : Nat → Old.Q)
    (hs : ∀ i, i<25 → Canonical (sem i)) (hp : ∀ i, i<10 → Canonical (p i))
    {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (hash : H) (c1 : Array U8 32#usize)
    (transcript : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (hprep : AspisR1PublicPreparation.r1_semantic.public_transcript D
      (AspisR1PublicPreparation.PreparationBinding.preparationPublic s) hash c1=ok (.Ok transcript)) :
    ∃ (z : Array Selected 16#usize) (mask : Array Selected 10#usize) (g terminal : Selected),
      run s sem p=ok (.Ok (terminal,z,mask,g)) ∧ Canonical (fromSelected terminal) ∧
      decode (fromSelected terminal)=R0P.SemSource.terminalValue (publicModel s)
        (decode (sem 0)) (decode (sem 1)) (decode (sem 2)) (decode (sem 13))
        (fun i : Fin 10 => decode (sem (3+i.val))) ProverCommitQBasis51.basis
        (fun _ _ => 0) (ProverCommitSuccessorPoint49.decoded p) := by
  have hzero : AspisR1.SemanticCompositionCoefficients.CanonicalArray zeroClaims :=
    array_canonical 84#usize (fun _ => zero) (fun _ _ => zero_canonical)
  have hzc : AspisR1.SemanticCompositionCoefficients.CanonicalArray (zc sem) :=
    array_canonical 10#usize (fun i => sem (3+i)) (by intro i hi;apply hs;change 3+i<25;change i<10 at hi;omega)
  obtain ⟨z,mask,g,terminal,hrun,hcan,hvalue⟩ := ProverCommitTerminalQName55.source_success
    (array 10#usize p) (zc sem) s zeroClaims
    (toSelected (sem 0)) (toSelected (sem 1)) (toSelected (sem 2)) (toSelected (sem 13))
    (array_canonical 10#usize p hp) hzc hzero
    (canonical_to _ (hs 0 (by decide))) (canonical_to _ (hs 1 (by decide)))
    (canonical_to _ (hs 2 (by decide))) (canonical_to _ (hs 13 (by decide)))
    D hash c1 transcript hprep
  refine ⟨z,mask,g,terminal,hrun,canonical_from terminal hcan,?_⟩
  rw [decode_from]
  rw [claims_zero,point_model] at hvalue
  change AspisR1.ExtractedMaskQM31Exact.decode terminal=R0P.SemSource.terminalValue (publicModel s)
    (AspisR1.ExtractedMaskQM31Exact.decode (toSelected (sem 0)))
    (AspisR1.ExtractedMaskQM31Exact.decode (toSelected (sem 1)))
    (AspisR1.ExtractedMaskQM31Exact.decode (toSelected (sem 2)))
    (AspisR1.ExtractedMaskQM31Exact.decode (toSelected (sem 13)))
    (AspisR1.SelectorMarginalModel.modelPoint (zc sem)) ProverCommitQBasis51.basis
    (fun _ _ => 0) (ProverCommitSuccessorPoint49.decoded p) at hvalue
  have hzcpoint : AspisR1.SelectorMarginalModel.modelPoint (zc sem)=
      (fun i : Fin 10 => decode (sem (3+i.val))) := point_model (fun i => sem (3+i))
  rw [hzcpoint] at hvalue
  simpa only [decode_to] using hvalue

#print axioms claims_zero
#print axioms exact_result
end R1Z.ProverCommitTerminalZero55
