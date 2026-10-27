import TxS_Finish
import TxS_Transfer
import TxS_Query
import Cons_NativeBuild
import FinT_Model
import AuS1_Recovery
set_option autoImplicit false
noncomputable section
namespace AspisR1.TxS_FinishProof
open Aeneas Aeneas.Std Result
open scoped BigOperators
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft
attribute [local instance] Classical.propDecidable

theorem strengthen {F C Hash : Type} (base : VTop_Stages.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps F) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (queryLeaves : Port5Q1_QueryPorts.SessionAPrimitives query)
    (geo : Port3_NativeGeometryBody.Ops C) (geoLeaves : Port5Q1_GeometryCanonical.SessionAPrimitives geo)
    (domain : Port5Q1_Domain.SessionADomain geo)
    (multiply : geo.op9 = AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : geo.op7 = ok 1#u32) (inverse : geo.op11 = Port4C_InverseExecution.inverse_owned)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8) (saved : alloc.vec.Vec U8)
    (H : Bytes → State) (stored publicBytes : Bytes)
    {CurrentHash : Type} (installed : AspisR1CurrentCaller.Ops)
    (currentD : AspisR1CurrentCaller.aspis_core.digest.Digest32 CurrentHash) (currentHash : CurrentHash)
    (semanticPublic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub1 proof1 : Slice U8) (split : Usize)
    (run : Tx1Q_Execution.Run installed reserved query geo currentD currentHash semanticPublic pub1 proof1 split saved)
    (sourceSize : (Tx1Q_Carriers.accumulator {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩}).weights.val.length=64)
    (qb : ∀ j : Fin 22,((Tx1Q_Carriers.prepared run.p).queries.val[j.val]'(by have h : (Tx1Q_Carriers.prepared run.p).queries.val.length=22:=(Tx1Q_Carriers.prepared run.p).queries.property;omega)).val<262144)
    (canonicalBody : CheckpointBytesBlocks.CanonicalFields (Port3_DecodeCoherence.inventory
      (Tx1Q_Carriers.prepared run.p) (Tx1Q_Carriers.accumulator {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩}) sourceSize qb))
    (parsed : Parsed)
    (trace : List (Bytes × State)) (frame : Bytes)
    (wire : parsed.wire = bytesOf proof.val)
    (same : bytesOf checkpoint.val = bytesOf saved.val)
    (proofLength : proof.val.length = 57607)
    (t : Cons_Native.Witness)
    (calls : Cons_Native.Calls base finish reserved query geo D hash pub proof checkpoint t)
    (aux : Cons_NativeBuild.Aux reserved query geo D hash pub proof checkpoint t)
    (body : CheckpointBytes4SavedFields.BodyMatches t.p2 t.saved2
      (CheckpointBytesBlocks.prepared (Port3_DecodeCoherence.inventory
        (Tx1Q_Carriers.prepared run.p) (Tx1Q_Carriers.accumulator {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩}) sourceSize qb) canonicalBody)
      (CheckpointBytes5Output.accumulator (Tx1Q_Carriers.accumulator {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩})))
    (sameAccumulator : CheckpointBytes5Output.accumulator t.saved2=CheckpointBytes5Output.accumulator
      (Tx1Q_Carriers.accumulator {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩}))
    (wire1 : bytesOf proof1.val=bytesOf proof.val)
    (auth : ∀ (data : MatchingSupport.Data OraclePortCheckpointAbiC5.E)
      (rho : OraclePortCheckpointAbiC5.K) (q : Fin 22 → Fin 262144),
      Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared run.p) data q rho →
      AuS1_Finish.Collision H trace parsed q ∨
        ∀ pos, pos < 22 → OraclePortAllSelectedRecoveryC6.recovered trace frame parsed 2 (index q 2 pos) =
          some (OraclePortPackedChoiceC4.payload parsed 2 pos)) :
    TxS_Finish.Outcome finish t.v2 t.p2 {t.returned2 with weights := t.back2 t.flushed2}
      proof saved H stored publicBytes run.p parsed trace := by
  rcases t with ⟨p2,saved2,g2,geometry2,pending2,returned2,after2,flushed2,back2,v2⟩
  obtain ⟨hr,hnext,hgeo,hpending,hquery,hback,hflush⟩ := aux
  have ⟨_,_,_,_,_,_,_,_,_,finishCall,_⟩ := calls
  obtain ⟨s2,alpha0,alpha1,alphas,ha0,ha1,has⟩ :=
    T2R_Reader.observations base reserved query geo D hash checkpoint proof pub p2 saved2 calls.1
  refine ⟨s2,alpha0,alpha1,alphas,ha0,ha1,has,?_⟩
  intro r0 r1 weights pair dot hw hp hd
    semantic q tr i hi hq read decoded pairing matchesLaw equation dotLaw canonical prepare
  rcases auth i.data (SelectedChallengeMap.rhoOf i.rho) q prepare with collision | indexed
  · exact Or.inl collision
  · right
    have indexed' : ∀ pos, pos < 22 →
        OraclePortAllSelectedRecoveryC6.recovered trace frame parsed 2 (index q 2 pos) =
          some (OraclePortPackedChoiceC4.payload ⟨bytesOf proof.val,semantic⟩ 2 pos) := by
      intro pos bound
      simpa only [OraclePortPackedChoiceC4.payload,OraclePortSelectedDraft.opening,wire] using indexed pos bound
    have sourceRead : LiteralMatchingData.read (OraclePortStoredDecisionDraftC4.typedRows
        (⟨bytesOf proof1.val,semantic⟩ : OraclePortCompactDraft.Parsed) q tr)=some i.data := by
      rw [wire1];exact read
    have proofLength1 : proof1.val.length=57607 := by
      have lengths := congrArg List.length wire1
      simpa only [bytesOf,List.length_map,proofLength] using lengths
    have indexed1 : ∀ pos, pos<22 →
      OraclePortAllSelectedRecoveryC6.recovered trace frame parsed 2 (index q 2 pos)=
        some (OraclePortPackedChoiceC4.payload ⟨bytesOf proof1.val,semantic⟩ 2 pos) := by
      rw [wire1];exact indexed'
    have ten := Tx1Q_Model.ten installed reserved query geo currentD currentHash semanticPublic pub1 proof1 split saved run
      queryLeaves ⟨bytesOf proof1.val,semantic⟩ q tr i.data (SelectedChallengeMap.rhoOf i.rho)
      prepare sourceRead rfl proofLength1 (OraclePortAllSelectedRecoveryC6.recovered trace frame parsed 2)
      indexed1 geoLeaves domain multiply one inverse
    have fields := TxS_Transfer.prepare (Tx1Q_Carriers.prepared run.p) p2 _ saved2
      sourceSize qb canonicalBody _ body i.data (SelectedChallengeMap.rhoOf i.rho) q prepare
    rw [hnext] at hgeo
    have geometry := Port5Q1_GeometryReads.accepted geo geoLeaves domain multiply one inverse
      p2.queries 10#usize 22#usize geometry2 (by decide) hgeo
    have twelve := TxS_Query.twelve query queryLeaves proof p2 saved2 returned2 g2 geometry2 pending2 after2
      flushed2 back2 ⟨bytesOf proof.val,semantic⟩ q tr i.data (SelectedChallengeMap.rhoOf i.rho)
      fields.1 fields.2.1 fields.2.2.1 fields.2.2.2 hnext read rfl proofLength (OraclePortAllSelectedRecoveryC6.recovered trace frame parsed 2)
      indexed' geometry reserved hpending hquery hback hflush
    have values := FinT_Model.finish_value finish v2 p2 _ saved2 alpha0 alpha1 r0 r1 weights alphas pair dot
      s2 ha0 ha1 hw has hp hd ⟨bytesOf proof.val,semantic⟩ q tr i hi hq read decoded pairing
      matchesLaw equation dotLaw canonical (sameAccumulator.trans ten.1) twelve
    refine ⟨values.1,values.2,?_⟩
    rw [← values.2]
    simp only [finishCall,decide_true]

#print axioms strengthen
end AspisR1.TxS_FinishProof
end
