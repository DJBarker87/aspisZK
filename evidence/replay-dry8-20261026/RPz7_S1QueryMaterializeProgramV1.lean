import RPz7_S1QueryMaterializePairsV1
import S1QueryOverwriteEightV1
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.PreparedQueryMaterialize
open Aeneas Aeneas.Std Result
open PreparedHashCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw
open AspisS1QueryArrayOperations AspisS1QueryOverwriteEight

def normalMaterialize (state0 : Bytes32) : Program Bytes State (Result (Blocks8 × Blocks8)) :=
  .ask (flatten (TranscriptStep.readParts state0 1#u8)) fun b0 =>
  .ask (flatten (TranscriptStep.readParts state0 2#u8)) fun x0 =>
  .ask (flatten (TranscriptStep.readParts (encodeState x0) 1#u8)) fun b1 =>
  .ask (flatten (TranscriptStep.readParts (encodeState x0) 2#u8)) fun x1 =>
  .ask (flatten (TranscriptStep.readParts (encodeState x1) 1#u8)) fun b2 =>
  .ask (flatten (TranscriptStep.readParts (encodeState x1) 2#u8)) fun x2 =>
  .ask (flatten (TranscriptStep.readParts (encodeState x2) 1#u8)) fun b3 =>
  .ask (flatten (TranscriptStep.readParts (encodeState x2) 2#u8)) fun x3 =>
  .ask (flatten (TranscriptStep.readParts (encodeState x3) 1#u8)) fun b4 =>
  .ask (flatten (TranscriptStep.readParts (encodeState x3) 2#u8)) fun x4 =>
  .ask (flatten (TranscriptStep.readParts (encodeState x4) 1#u8)) fun b5 =>
  .ask (flatten (TranscriptStep.readParts (encodeState x4) 2#u8)) fun x5 =>
  .ask (flatten (TranscriptStep.readParts (encodeState x5) 1#u8)) fun b6 =>
  .ask (flatten (TranscriptStep.readParts (encodeState x5) 2#u8)) fun x6 =>
  .ask (flatten (TranscriptStep.readParts (encodeState x6) 1#u8)) fun b7 =>
  .ask (flatten (TranscriptStep.readParts (encodeState x6) 2#u8)) fun x7 =>
  .done (ok (Array.make 8#usize [encodeState b0,encodeState b1,encodeState b2,encodeState b3,encodeState b4,encodeState b5,encodeState b6,encodeState b7],
    Array.make 8#usize [encodeState x0,encodeState x1,encodeState x2,encodeState x3,encodeState x4,encodeState x5,encodeState x6,encodeState x7]))

/-- Complete source arrays and ordered oracle program, not just a read set.
Every source array operation is total at its proved fixed index. -/
theorem materialize_program {H : Type} (D : aspis_core.Digest32 H) (hash : H) (state : Bytes32) :
    oracleProgram (materialize effects D hash state)=normalMaterialize state := by
  rw [materialize_code_eq_pairs]
  have mut0 : ∀ a : Blocks8, Array.index_mut_usize a 0#usize=
      ok (a.val[0]'(by have := a.property; simp_all),fun value => a.set 0#usize value) := by
    intro a
    exact index_mut_total a 0#usize (by decide)
  have read0 : ∀ (a : Blocks8) (value : Bytes32), Array.index_usize (a.set 0#usize value) 0#usize=ok value :=
    fun a value => QueryPair.index_set a 0#usize value (by decide)
  have step1 : ∀ (s : Bytes32) (blocks advances : Blocks8),
      oracleProgram (QueryPair.pairStep D hash s blocks advances 1#usize)=
        Program.ask (flatten (TranscriptStep.readParts s 1#u8)) (fun b =>
          Program.ask (flatten (TranscriptStep.readParts s 2#u8)) (fun x =>
            .done (ok (encodeState x,blocks.set 1#usize (encodeState b),advances.set 1#usize (encodeState x))))) :=
    fun s blocks advances => QueryPair.pairStep_program D hash s blocks advances 1#usize (by decide)
  have step2 : ∀ (s : Bytes32) (blocks advances : Blocks8),
      oracleProgram (QueryPair.pairStep D hash s blocks advances 2#usize)=
        Program.ask (flatten (TranscriptStep.readParts s 1#u8)) (fun b =>
          Program.ask (flatten (TranscriptStep.readParts s 2#u8)) (fun x =>
            .done (ok (encodeState x,blocks.set 2#usize (encodeState b),advances.set 2#usize (encodeState x))))) :=
    fun s blocks advances => QueryPair.pairStep_program D hash s blocks advances 2#usize (by decide)
  have step3 : ∀ (s : Bytes32) (blocks advances : Blocks8),
      oracleProgram (QueryPair.pairStep D hash s blocks advances 3#usize)=
        Program.ask (flatten (TranscriptStep.readParts s 1#u8)) (fun b =>
          Program.ask (flatten (TranscriptStep.readParts s 2#u8)) (fun x =>
            .done (ok (encodeState x,blocks.set 3#usize (encodeState b),advances.set 3#usize (encodeState x))))) :=
    fun s blocks advances => QueryPair.pairStep_program D hash s blocks advances 3#usize (by decide)
  have step4 : ∀ (s : Bytes32) (blocks advances : Blocks8),
      oracleProgram (QueryPair.pairStep D hash s blocks advances 4#usize)=
        Program.ask (flatten (TranscriptStep.readParts s 1#u8)) (fun b =>
          Program.ask (flatten (TranscriptStep.readParts s 2#u8)) (fun x =>
            .done (ok (encodeState x,blocks.set 4#usize (encodeState b),advances.set 4#usize (encodeState x))))) :=
    fun s blocks advances => QueryPair.pairStep_program D hash s blocks advances 4#usize (by decide)
  have step5 : ∀ (s : Bytes32) (blocks advances : Blocks8),
      oracleProgram (QueryPair.pairStep D hash s blocks advances 5#usize)=
        Program.ask (flatten (TranscriptStep.readParts s 1#u8)) (fun b =>
          Program.ask (flatten (TranscriptStep.readParts s 2#u8)) (fun x =>
            .done (ok (encodeState x,blocks.set 5#usize (encodeState b),advances.set 5#usize (encodeState x))))) :=
    fun s blocks advances => QueryPair.pairStep_program D hash s blocks advances 5#usize (by decide)
  have step6 : ∀ (s : Bytes32) (blocks advances : Blocks8),
      oracleProgram (QueryPair.pairStep D hash s blocks advances 6#usize)=
        Program.ask (flatten (TranscriptStep.readParts s 1#u8)) (fun b =>
          Program.ask (flatten (TranscriptStep.readParts s 2#u8)) (fun x =>
            .done (ok (encodeState x,blocks.set 6#usize (encodeState b),advances.set 6#usize (encodeState x))))) :=
    fun s blocks advances => QueryPair.pairStep_program D hash s blocks advances 6#usize (by decide)
  have step7 : ∀ (s : Bytes32) (blocks advances : Blocks8),
      oracleProgram (QueryPair.pairStep D hash s blocks advances 7#usize)=
        Program.ask (flatten (TranscriptStep.readParts s 1#u8)) (fun b =>
          Program.ask (flatten (TranscriptStep.readParts s 2#u8)) (fun x =>
            .done (ok (encodeState x,blocks.set 7#usize (encodeState b),advances.set 7#usize (encodeState x))))) :=
    fun s blocks advances => QueryPair.pairStep_program D hash s blocks advances 7#usize (by decide)
  have overwrite : ∀ (a : Blocks8) (x0 x1 x2 x3 x4 x5 x6 x7 : Bytes32),
      ((((((((a.set 0#usize x0).set 1#usize x1).set 2#usize x2).set 3#usize x3).set
        4#usize x4).set 5#usize x5).set 6#usize x6).set 7#usize x7)=
      Array.make 8#usize [x0,x1,x2,x3,x4,x5,x6,x7] := writeEight_eq_make
  unfold materializePairs normalMaterialize
  simp only [oracleProgram_bind,QueryPair.readState_program,oracleProgram_lift,oracleProgram_pure,
    mut0,read0,step1,step2,step3,step4,step5,step6,step7,AspisV8R19.OracleProgramOps.bind,continueOracle,overwrite]

#print axioms materialize_program
end AspisR1PublicPreparation.PreparedQueryMaterialize
