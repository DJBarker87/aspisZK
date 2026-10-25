import F3J_InitialLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_InitialValue
open Aeneas Aeneas.Std Result FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1PublicPreparation SourceDigestAddresses SourceDigestLog SourceGlobalOracleInitial

theorem initial {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (c : SourceFull25.Call D pre)
    {pubInput : pool_v1.pair_forest_semantic_terminal.r0.Public} {root : TranscriptStep.Bytes32}
    (init : PublicInitCall D pubInput root c.before)
    (number : c.row.val=0) (empty : rawBytes c.record.framed=PublicInitFrame.emptyRecord)
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (P : LiteralTranscript.Prefix) (word : LiteralTranscript.C1Word)
    (publicBytes : P.statement.pubBytes=rawBytes (alloc.vec.Vec.deref init.encoded)) :
    eval H (LiteralByteSampler.samp 0 P (.initial (decodeState root) word)).toProgram=
      (initPair init::callLog c,
       (TranscriptView.Value.ordinary (SourceLiteralTraceLift.sourceChallenge c),decodeState c.after.state)) := by
  have initCons : (initPair init).2=H (initPair init).1 :=
    backend _ ⟨c.before.hash,_,init.state,rfl,init.digest⟩
  have initLog : ∀ q ∈ [initPair init],q.2=H q.1 := by
    intro q hq
    have same : q=initPair init := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hq
    subst q
    exact initCons
  have initState := initializer_state_from_log init H [initPair init]
    (List.mem_cons_self) initLog P (decodeState root) publicBytes rfl
  have all : ∀ q ∈ sourceLog [c],q.2=H q.1 := by
    simpa only [sourceLog,List.flatMap_cons,List.flatMap_nil,List.append_nil] using
      F3J_SemanticLog.consistent c H backend
  have bound : ∀ d ∈ [c],(rawBytes d.record.framed).length≤SelectedTranscriptParams.params.D := by
    intro d hd
    have same : d=c := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hd
    subst d
    rw [empty]
    decide
  have value := call_simulates_literal_initial [c] c (List.mem_cons_self) H (sourceLog [c])
    (fun _ h => h) all bound number P (decodeState root) word initState empty
  apply Prod.ext
  · exact F3J_InitialLog.initial init c rfl number empty H backend P word publicBytes
  · rw [LiteralByteSampler.eval_eq]
    exact Prod.ext value.1.symm value.2.symm

#print axioms initial
end AspisR1.F3J_InitialValue
end
