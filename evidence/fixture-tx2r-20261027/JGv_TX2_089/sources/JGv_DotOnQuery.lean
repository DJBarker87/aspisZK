import JGv_DotFields
import JGv_DotCanonical
import JGo_TX2_Partial
import JGv_QueryScalars
import JGv_FlushMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_DotOnQuery
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem source (base : VTop_Stages.Ops) {C Hash : Type} (err : C)
    (geometry : Port3_NativeGeometryBody.Ops C) (query : Port3_NativeQueryBody.Ops)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    ∃ a b flushed dot,
      Op5T_Install.stageBatch Port4B_Install.leaves
        (JFn_HashBoundary.dictionary JFp_SHADigest.digest D)
        JFx_NativeBytes.proof JFo_Prepared.value JGe_View.folded 1#usize hash=ok (.Ok ()) ∧
      JFz_TX2_AccumulationChain.updates (JGc_TX2_QueryDictionary.input query) 12=ok (a,b) ∧
      (Tx2N_Install.inner base true (JGc_TX2_InstalledQuery.raw query)).op6
        JFx_NativeBytes.proof JFo_Prepared.value JFo_Prepared.accumulator JFr_TX2_Powers.value none
        (JFv_TX2_Geometry.value err geometry) JFo_Pending.value 22#usize=ok (.Ok (a,b)) ∧
      a.weights=JFo_Prepared.accumulator.weights ∧ a.next=22#usize ∧
      Port3_FlushInstall.flush b a.weights.deref=ok flushed ∧
      flushed.val.length=64 ∧ (∀ q∈flushed.val,Port3_FlushInstall.Canonical q) ∧
      a.rhs=JGv_QueryScalars11.rhs ∧ a.power=JGv_QueryScalars11.power ∧
      SAG_DotClosed.source (JFw_Frames.window 8007 2048)
        (JGo_TX2_Partial.writeback a flushed).weights.deref=ok (.Ok dot) ∧
      Port4C_QueryArithmetic.CanonE dot ∧
      ∀ i : Usize,i.val<64 → ∃ q,Slice.index_usize flushed i=ok q ∧
        ∀ k : Fin 4,((JGv_FlushMeaning.limb q k).val : JGv_QueryRows.F)=JGv_QueryRows.weights 12 i.val k := by
  obtain ⟨a,b,flushed,root,batch,updates,call,weights,next,flush,size,canon⟩ :=
    JGo_TX2_BatchQuery.source base err geometry query D hash
  have scalars := JGv_QueryScalars.source err geometry (JGc_TX2_QueryDictionary.input query) a b updates
  obtain ⟨dot,dotCall⟩ := JGv_DotTotal.source (JFw_Frames.window 8007 2048) flushed size JGv_DotFields.source canon
  have dotCanon := JGv_DotCanonical.source (JFw_Frames.window 8007 2048) flushed dot size JGv_DotFields.source canon dotCall
  exact ⟨a,b,flushed,dot,batch,updates,call,weights,next,flush,size,canon,scalars.1,scalars.2,
    dotCall,dotCanon,JGv_FlushMeaning.source err geometry (JGc_TX2_QueryDictionary.input query) a b flushed updates flush⟩
#print axioms source
end AspisR1.JGv_DotOnQuery
end
