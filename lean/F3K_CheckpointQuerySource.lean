import F3K_CheckpointQueryNumeric
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_CheckpointQuerySource
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
variable {Hash : Type} {D : aspis_core.Digest32 Hash} {B : PreparedScratchModel.Boundaries}
    {embed : aspis_core.field.M31 → Result aspis_core.field.WideExact}
    {sem : r1_semantic.Verified Hash} {v : verifier.View} {hash : Hash} {p : OraclePortCompactDraft.Parsed}
    {out : verifier.Prepared} {scratch : Array aspis_core.field.WideExact 29#usize}

theorem source (s : F3K_OpeningSpine.Spine D B embed sem v hash p out scratch) :
    ∃ q, LiteralQueryRead.decode ((F3K_CheckpointPreparedFields.writerPrepared out).queries.val.map (fun x=>x.val))=some q ∧
      CheckpointBytes5Output.queries (Tx1Q_Carriers.prepared (AspisR1CurrentCaller.InstalledPreparation.currentPrepared out))=q := by
  obtain ⟨q,decoded,coords,bounds⟩ := F3K_CheckpointPreparedFields.queries s
  exact ⟨q,decoded,F3K_CheckpointQueryNumeric.exact_queries _ q coords⟩
#print axioms source
end AspisR1.F3K_CheckpointQuerySource
end
