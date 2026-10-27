import F3K_PreparedSourceFields
import GExp_FirstCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_CheckpointPreparedFields
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation

def writerPrepared (out : verifier.Prepared) : CheckpointBytes5Writer.Prepared :=
  CheckpointBytes3Namespaces.toPrepared (Tx1Q_Carriers.prepared (AspisR1CurrentCaller.InstalledPreparation.currentPrepared out))

variable {Hash : Type} {D : aspis_core.Digest32 Hash} {B : PreparedScratchModel.Boundaries}
    {embed : aspis_core.field.M31 → Result aspis_core.field.WideExact}
    {sem : r1_semantic.Verified Hash} {v : verifier.View} {hash : Hash} {p : OraclePortCompactDraft.Parsed}
    {out : verifier.Prepared} {scratch : Array aspis_core.field.WideExact 29#usize}

theorem variant (s : F3K_OpeningSpine.Spine D B embed sem v hash p out scratch)
    (hv : v.variant=.S2) : (writerPrepared out).variant=.S2 := by
  have eq := (F3K_PreparedSourceFields.fields s).1.trans hv
  change CheckpointBytes3Namespaces.toVariant (Tx1Q_Carriers.variant
    (AspisR1CurrentCaller.InstalledPreparation.currentVariant out.variant))=_
  rw [eq]
  rfl

theorem queries (s : F3K_OpeningSpine.Spine D B embed sem v hash p out scratch) :
    ∃ q,LiteralQueryRead.decode ((writerPrepared out).queries.val.map (fun x=>x.val))=some q ∧
      (∀ j : Fin 22,((writerPrepared out).queries.val[j.val]'(by have len : (writerPrepared out).queries.val.length=22:=(writerPrepared out).queries.property;omega)).val=(q j).val) ∧
      (∀ j : Fin 22,((writerPrepared out).queries.val[j.val]'(by have len : (writerPrepared out).queries.val.length=22:=(writerPrepared out).queries.property;omega)).val<262144) := by
  exact F3K_PreparedSourceFields.query_binding s

theorem state (s : F3K_OpeningSpine.Spine D B embed sem v hash p out scratch) :
    (writerPrepared out).state=s.c.t6.state := by
  exact (F3K_PreparedSourceFields.fields s).2.2.2.2.2.2.1

#print axioms variant
#print axioms queries
#print axioms state
end AspisR1.F3K_CheckpointPreparedFields
end
