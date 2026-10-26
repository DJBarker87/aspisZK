import RPz7_F3J_SemanticLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_InitialLog
open Aeneas Aeneas.Std Result FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1PublicPreparation SourceDigestAddresses SourceDigestLog SourceGlobalOracleInitial

theorem initial {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    {pubInput : pool_v1.pair_forest_semantic_terminal.r0.Public}
    {root : TranscriptStep.Bytes32} {before : r1_wire.SemanticTranscript Hash}
    (init : PublicInitCall D pubInput root before)
    (c : SourceFull25.Call D pre) (first : c.before=before) (number : c.row.val=0)
    (empty : rawBytes c.record.framed=PublicInitFrame.emptyRecord)
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (P : LiteralTranscript.Prefix) (word : LiteralTranscript.C1Word)
    (publicBytes : P.statement.pubBytes=rawBytes (alloc.vec.Vec.deref init.encoded)) :
    (eval H (LiteralByteSampler.samp 0 P (.initial (decodeState root) word)).toProgram).1=
      initPair init::callLog c := by
  let params := SelectedTranscriptParams.params
  have initCons : (initPair init).2=H (initPair init).1 :=
    backend _ ⟨before.hash,_,init.state,rfl,init.digest⟩
  have initLog : ∀ q ∈ [initPair init],q.2=H q.1 := by
    intro q hq
    have same : q=initPair init := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hq
    subst q
    exact initCons
  have initState := initializer_state_from_log init H [initPair init]
    (List.mem_cons_self) initLog P (decodeState root) publicBytes rfl
  rw [← first] at initState
  have bound : (rawBytes c.record.framed).length≤params.D := by
    rw [empty]; decide
  have tag : decodeByte c.tag=params.lbl 0 := by
    apply Fin.ext
    change c.tag.val=(SelectedTranscriptParams.label 0).val
    rw [SelectedTranscriptParams.label_val 0 (by decide),c.tag_code,c.record_row,number]
  have address : flatten (TranscriptStep.absorbParts c.before.state c.tag c.record.framed)=
      (PublicInitFrame.row0 params (by decide)
        (H (PublicInitFrame.addr P.statement.pubBytes P.statement.initFits (decodeState root)).toBytes)).toBytes := by
    rw [absorb_address params _ _ _ bound]
    apply congrArg Addr.toBytes
    apply Subtype.ext
    simp only [absorbA,PublicInitFrame.row0,tag,empty,initState]
    rfl
  have cons := F3J_SemanticLog.consistent c H backend
  have ha := cons _ (List.mem_cons_self)
  have hb := cons _ (List.mem_cons_of_mem _ (List.mem_cons_self))
  have hs := cons _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
  change decodeState c.absorbed=H (flatten _) at ha
  change decodeState c.block=H (flatten _) at hb
  change decodeState c.state=H (flatten _) at hs
  rw [address] at ha
  rw [squeeze_address params] at hb
  rw [advance_address params] at hs
  rw [LiteralByteSampler.eval_eq]
  change (mapView Addr.toBytes (eval (fun a => H a.toBytes)
    (DuplexSamplers.initial params (PublicInitFrame.addr P.statement.pubBytes P.statement.initFits (decodeState root))
      (PublicInitFrame.row0 params _) 0 TranscriptView.liftChallenge).toProgram)).1=_
  rw [DuplexSamplers.initial_eval]
  simp only [mapView,List.map_cons,List.map_nil]
  rw [← ha,← hb,← hs]
  have initAddr : (initPair init).1=(PublicInitFrame.addr P.statement.pubBytes P.statement.initFits (decodeState root)).toBytes := by
    have hL : 75+(rawBytes (alloc.vec.Vec.deref init.encoded)).length≤SelectedTranscriptParams.L := by
      rw [← publicBytes]; exact P.statement.initFits
    change flatten _=_
    rw [init_address _ _ _ (successful_length _ _ init.converted) hL]
    apply congrArg Addr.toBytes
    apply Subtype.ext
    simp only [PublicInitFrame.addr,publicBytes]
  have initOut : (initPair init).2=H (PublicInitFrame.addr P.statement.pubBytes P.statement.initFits (decodeState root)).toBytes := by
    rw [← initAddr]; exact initCons
  rw [← address]
  simp only [callLog,squeeze_address params,advance_address params]
  exact congrArg₂ List.cons (Prod.ext initAddr.symm initOut.symm) rfl

#print axioms initial
end AspisR1.F3J_InitialLog
end
