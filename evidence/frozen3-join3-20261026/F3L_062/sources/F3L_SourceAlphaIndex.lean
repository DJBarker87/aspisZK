import F3L_SourceNumeric
set_option autoImplicit false
namespace AspisR1.F3L_SourceAlphaIndex
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisR1CurrentCaller.InstalledPreparation

theorem alpha1 {Hash : Type} {D : aspis_core.Digest32 Hash} {B : PreparedScratchModel.Boundaries}
    {embed : aspis_core.field.M31 → Result aspis_core.field.WideExact}
    {sem : r1_semantic.Verified Hash} {v : verifier.View} {hash : Hash}
    {p : OraclePortCompactDraft.Parsed} {out : verifier.Prepared}
    {scratch : Array aspis_core.field.WideExact 29#usize}
    (spine : F3K_OpeningSpine.Spine D B embed sem v hash p out scratch)
    (alpha : AspisR1Stage2.aspis_core.field.wide_exact.WideExact)
    (read : Array.index_usize (Tx1Q_Carriers.prepared (currentPrepared out)).alpha 1#usize=ok alpha) :
    alpha=Tx1Q_Carriers.e (currentE spine.c.alpha1) := by
  have array := (F3K_PreparedSourceFields.fields spine).2.2.2.1
  change Array.index_usize
    (Tx1Q_Carriers.arr Tx1Q_Carriers.e (AspisR1ClaimPreparedBridge.mapArray currentE out.alpha)) 1#usize=ok alpha at read
  rw [array] at read
  have same : ok (Tx1Q_Carriers.e (currentE spine.c.alpha1))=ok alpha := by
    simpa only [Array.index_usize,Tx1Q_Carriers.arr,AspisR1ClaimPreparedBridge.mapArray,
      Array.make,List.map_cons,List.map_nil] using read
  exact (Result.ok.inj same).symm

#print axioms alpha1
end AspisR1.F3L_SourceAlphaIndex
