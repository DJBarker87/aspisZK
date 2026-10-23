import R1Z.ProverCommitStreamSource
set_option autoImplicit false
noncomputable section
namespace R1Z.RealR2_Context
open Aeneas Aeneas.Std Result WP
open AspisR1ProverStreams

/-- Encoding is total for every context, including adversarial nonces and
fingerprints; it makes no hash calls and requires no admission premise. -/
theorem encode_total (c : aspis_core.state_only_hiding.StateOnlyHidingContext) :
    ∃ encoded, aspis_core.state_only_hiding.StateOnlyHidingContext.encode c = ok encoded := by
  have h : aspis_core.state_only_hiding.StateOnlyHidingContext.encode c ⦃ _ => True ⦄ := by
    unfold aspis_core.state_only_hiding.StateOnlyHidingContext.encode
    step* <;> scalar_tac
  exact (spec_imp_exists h).imp (fun _ h => h.1)

/-- List model of the four disjoint fixed-width writes, without array borrows. -/
def frame (c : aspis_core.state_only_hiding.StateOnlyHidingContext) : List U8 :=
  let initial := (List.replicate 81 0#u8).set 0 1#u8
  let digest := initial.setSlice! 1 c.statement_digest.val
  let nonce := digest.setSlice! 33 c.mask_nonce.val
  let mask := nonce.setSlice! 65 (c.mask_layout_fingerprint.bv.toLEBytes.map UScalar.mk)
  mask.setSlice! 73 (c.layout_factor_fingerprint.bv.toLEBytes.map UScalar.mk)

theorem encode_frame (c : aspis_core.state_only_hiding.StateOnlyHidingContext) :
    aspis_core.state_only_hiding.StateOnlyHidingContext.encode c
      ⦃ e => e.val = frame c ⦄ := by
  unfold aspis_core.state_only_hiding.StateOnlyHidingContext.encode
  step* <;> first | scalar_tac | simp_all [frame, Array.set, Array.repeat,
    Array.to_slice, aspis_core.state_only_hiding.STATE_ONLY_HIDING_CONTEXT_VERSION]

#print axioms encode_frame
#print axioms encode_total
end R1Z.RealR2_Context
