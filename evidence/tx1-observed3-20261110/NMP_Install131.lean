import NMP_ResultTransport
import NHG_PublicTranscript
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
  (AspisR1PublicPreparation.r1_semantic.public_transcript (digest d) (toT9 p) hash root)
theorem same {H : Type} (d : NMP_prepare.aspis_core.digest.Digest32 H)
 (p : NMP_prepare.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (hash : H) (root : Array U8 32#usize) :
 outer (inner toT10 toT12) (publicTranscript d p hash root) =
 AspisR1PublicPreparation.r1_semantic.public_transcript (digest d) (toT9 p) hash root := by
 apply outer_inverse
 intro r
 exact inner_inverse fromT10 toT10 fromT12 toT12 fromT10_inverse fromT12_inverse r
/-- CLOSED131's full source theorem at these exact public/hash/root arguments. -/
theorem source {H : Type} (d : NMP_prepare.aspis_core.digest.Digest32 H)
 (p : NMP_prepare.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (hash : H) (root : Array U8 32#usize) :
 outer (inner toT10 toT12) (publicTranscript d p hash root) =
 NHG_PublicTranscript.computation (digest d) (toT9 p) hash root :=
 (same d p hash root).trans (NHG_PublicTranscript.source _ _ _ _)
#print axioms same
#print axioms source
end AspisR1.NMP_Install131
