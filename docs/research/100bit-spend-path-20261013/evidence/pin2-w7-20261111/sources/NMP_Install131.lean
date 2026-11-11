import NMP_ResultTransport
import NHG_PublicTranscript
import PIN2_S1SemanticCodeVerifyExactV1
/-! PIN2 W10 (2026-11-11), coordinator-approved DEFINITION CHANGE: the installed
public-transcript child `publicTranscript` is the outer/inner transport of the erased PIN2
lifted public transcript on the frozen carriers,
`PreparedHashCode.erase (S1SemanticCode.publicTranscriptPIN2 (digest d) (toT9 p) hash root)`
(release: frozen `r1_semantic.public_transcript (digest d) (toT9 p) hash root`), so that the NNG 137
agreements with the PIN2 library child `LIB_VPublicTranscript.code` stay true.
STATEMENT CHANGES: `same` right-hand side is that erased PIN2 call (proof text unchanged);
`source` right-hand side is the copied-back PIN2 `public_transcript` on the copies
`rmap (cres transcriptBack errorBack) (PIN2 r1_semantic.public_transcript (PIN2W7_TranscriptCopy.digest (digest d)) (toPIN2 (toT9 p)) hash root)`
(release: the frozen `NHG_PublicTranscript.computation`), via `publicTranscriptPIN2_erasure`.
`source` has no consumer in the release tree (only #print axioms in the combined imports).
`digest` unchanged. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_Install131
open Aeneas Aeneas.Std Result NMP_ResultTransport NMP_Transport
/-- Only the type name of Digest32 differs; methods and Copy are identical. -/
def digest {H : Type} (d : NMP_prepare.aspis_core.digest.Digest32 H) : AspisR1PublicPreparation.aspis_core.Digest32 H :=
 ⟨d.coremarkerCopyInst,d.digest⟩
def publicTranscript {H : Type} (d : NMP_prepare.aspis_core.digest.Digest32 H)
 (p : NMP_prepare.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (hash : H) (root : Array U8 32#usize) :=
 outer (inner fromT10 fromT12)
  (AspisR1PublicPreparation.PreparedHashCode.erase
   (AspisR1PublicPreparation.S1SemanticCode.publicTranscriptPIN2 (digest d) (toT9 p) hash root))
theorem same {H : Type} (d : NMP_prepare.aspis_core.digest.Digest32 H)
 (p : NMP_prepare.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (hash : H) (root : Array U8 32#usize) :
 outer (inner toT10 toT12) (publicTranscript d p hash root) =
 AspisR1PublicPreparation.PreparedHashCode.erase
  (AspisR1PublicPreparation.S1SemanticCode.publicTranscriptPIN2 (digest d) (toT9 p) hash root) := by
 apply outer_inverse
 intro r
 exact inner_inverse fromT10 toT10 fromT12 toT12 fromT10_inverse fromT12_inverse r
/-- PIN2 full source theorem at these exact public/hash/root arguments: the copied-back
PIN2 `public_transcript` on the field copies. -/
theorem source {H : Type} (d : NMP_prepare.aspis_core.digest.Digest32 H)
 (p : NMP_prepare.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (hash : H) (root : Array U8 32#usize) :
 outer (inner toT10 toT12) (publicTranscript d p hash root) =
 AspisR1PublicPreparation.PIN2W7_PrefixGlue.rmap
  (AspisR1PublicPreparation.PIN2W7_PrefixGlue.cres AspisR1PublicPreparation.PIN2W7_PrefixGlue.transcriptBack
   AspisR1PublicPreparation.PIN2W7_PrefixGlue.errorBack)
  (AspisR1PublicPreparationPIN2.r1_semantic.public_transcript
   (AspisR1PublicPreparation.PIN2W7_TranscriptCopy.digest (digest d))
   (AspisR1PublicPreparation.PreparationBinding.toPIN2 (toT9 p)) hash root) :=
 (same d p hash root).trans (AspisR1PublicPreparation.S1SemanticCode.publicTranscriptPIN2_erasure _ _ _ _)
#print axioms same
#print axioms source
end AspisR1.NMP_Install131
