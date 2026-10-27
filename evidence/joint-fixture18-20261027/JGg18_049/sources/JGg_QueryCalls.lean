import JGg_QueryArrays
import S1ClosedPreparationHashCodeV1
set_option autoImplicit false
namespace AspisR1.JGg_QueryCalls
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.SqueezeOracleBridge
open AspisR1CurrentCaller.BorrowedClaimPrepared
attribute [local irreducible] JGg_Opening31.absorbed JGg_Opening31.payload
attribute [local irreducible] JGg_Opening31.block0 JGg_Opening31.block1 JGg_Opening31.block2 JGg_Opening31.block3 JGg_Opening31.block4 JGg_Opening31.block5 JGg_Opening31.block6 JGg_Opening31.block7
attribute [local irreducible] JGg_Opening31.next0 JGg_Opening31.next1 JGg_Opening31.next2 JGg_Opening31.next3 JGg_Opening31.next4 JGg_Opening31.next5 JGg_Opening31.next6 JGg_Opening31.next7
theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    ∃ q,QueriesModel.queries closedHashQueries D0
      (⟨encodeState JGg_Opening31.before,hash⟩ : transcript.Transcript Hash) 31#u8 JGg_Opening31.payload=
      ok (.Ok q,(⟨encodeState JGg_Opening31.next2,hash⟩ : transcript.Transcript Hash)) := by
  dsimp only
  obtain ⟨q,decode⟩ := JGg_QueryDecode.source
  have read0 : (AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)).digest hash
      (TranscriptStep.readParts (encodeState JGg_Opening31.absorbed) 1#u8)=ok (encodeState JGg_Opening31.block0) := by
    change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=_
    rw [JGg_Opening31.readHash0]
  have advance0 : (AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)).digest hash
      (TranscriptStep.readParts (encodeState JGg_Opening31.absorbed) 2#u8)=ok (encodeState JGg_Opening31.next0) := by
    change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=_
    rw [JGg_Opening31.advanceHash0]
  have read1 : (AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)).digest hash
      (TranscriptStep.readParts (encodeState JGg_Opening31.next0) 1#u8)=ok (encodeState JGg_Opening31.block1) := by
    change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=_
    rw [JGg_Opening31.readHash1]
  have advance1 : (AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)).digest hash
      (TranscriptStep.readParts (encodeState JGg_Opening31.next0) 2#u8)=ok (encodeState JGg_Opening31.next1) := by
    change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=_
    rw [JGg_Opening31.advanceHash1]
  have read2 : (AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)).digest hash
      (TranscriptStep.readParts (encodeState JGg_Opening31.next1) 1#u8)=ok (encodeState JGg_Opening31.block2) := by
    change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=_
    rw [JGg_Opening31.readHash2]
  have advance2 : (AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)).digest hash
      (TranscriptStep.readParts (encodeState JGg_Opening31.next1) 2#u8)=ok (encodeState JGg_Opening31.next2) := by
    change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=_
    rw [JGg_Opening31.advanceHash2]
  have read3 : (AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)).digest hash
      (TranscriptStep.readParts (encodeState JGg_Opening31.next2) 1#u8)=ok (encodeState JGg_Opening31.block3) := by
    change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=_
    rw [JGg_Opening31.readHash3]
  have advance3 : (AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)).digest hash
      (TranscriptStep.readParts (encodeState JGg_Opening31.next2) 2#u8)=ok (encodeState JGg_Opening31.next3) := by
    change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=_
    rw [JGg_Opening31.advanceHash3]
  have read4 : (AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)).digest hash
      (TranscriptStep.readParts (encodeState JGg_Opening31.next3) 1#u8)=ok (encodeState JGg_Opening31.block4) := by
    change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=_
    rw [JGg_Opening31.readHash4]
  have advance4 : (AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)).digest hash
      (TranscriptStep.readParts (encodeState JGg_Opening31.next3) 2#u8)=ok (encodeState JGg_Opening31.next4) := by
    change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=_
    rw [JGg_Opening31.advanceHash4]
  have read5 : (AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)).digest hash
      (TranscriptStep.readParts (encodeState JGg_Opening31.next4) 1#u8)=ok (encodeState JGg_Opening31.block5) := by
    change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=_
    rw [JGg_Opening31.readHash5]
  have advance5 : (AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)).digest hash
      (TranscriptStep.readParts (encodeState JGg_Opening31.next4) 2#u8)=ok (encodeState JGg_Opening31.next5) := by
    change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=_
    rw [JGg_Opening31.advanceHash5]
  have read6 : (AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)).digest hash
      (TranscriptStep.readParts (encodeState JGg_Opening31.next5) 1#u8)=ok (encodeState JGg_Opening31.block6) := by
    change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=_
    rw [JGg_Opening31.readHash6]
  have advance6 : (AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)).digest hash
      (TranscriptStep.readParts (encodeState JGg_Opening31.next5) 2#u8)=ok (encodeState JGg_Opening31.next6) := by
    change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=_
    rw [JGg_Opening31.advanceHash6]
  have read7 : (AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)).digest hash
      (TranscriptStep.readParts (encodeState JGg_Opening31.next6) 1#u8)=ok (encodeState JGg_Opening31.block7) := by
    change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=_
    rw [JGg_Opening31.readHash7]
  have advance7 : (AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)).digest hash
      (TranscriptStep.readParts (encodeState JGg_Opening31.next6) 2#u8)=ok (encodeState JGg_Opening31.next7) := by
    change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=_
    rw [JGg_Opening31.advanceHash7]
  refine ⟨q,?_⟩
  unfold QueriesModel.queries
  rw [JGg_Opening31.absorb]
  simp only [bind_tc_ok,lift,Array.to_slice]
  simp only [TranscriptStep.readParts,Array.to_slice] at read0 advance0 read1 advance1 read2 advance2 read3 advance3 read4 advance4 read5 advance5 read6 advance6 read7 advance7
  simp only [Array.make] at read0 advance0 read1 advance1 read2 advance2 read3 advance3 read4 advance4 read5 advance5 read6 advance6 read7 advance7
  rw [read0,bind_tc_ok]
  rw [JGg_QueryArrays.mutable,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [advance0,bind_tc_ok]
  simp only [JGg_QueryArrays.back_b,JGg_QueryArrays.back_a]
  rw [JGg_QueryArrays.state0,bind_tc_ok]
  rw [read1,bind_tc_ok,JGg_QueryArrays.b_update1,bind_tc_ok,advance1,bind_tc_ok,JGg_QueryArrays.a_update1,bind_tc_ok,JGg_QueryArrays.state1,bind_tc_ok]
  rw [read2,bind_tc_ok,JGg_QueryArrays.b_update2,bind_tc_ok,advance2,bind_tc_ok,JGg_QueryArrays.a_update2,bind_tc_ok,JGg_QueryArrays.state2,bind_tc_ok]
  rw [read3,bind_tc_ok,JGg_QueryArrays.b_update3,bind_tc_ok,advance3,bind_tc_ok,JGg_QueryArrays.a_update3,bind_tc_ok,JGg_QueryArrays.state3,bind_tc_ok]
  rw [read4,bind_tc_ok,JGg_QueryArrays.b_update4,bind_tc_ok,advance4,bind_tc_ok,JGg_QueryArrays.a_update4,bind_tc_ok,JGg_QueryArrays.state4,bind_tc_ok]
  rw [read5,bind_tc_ok,JGg_QueryArrays.b_update5,bind_tc_ok,advance5,bind_tc_ok,JGg_QueryArrays.a_update5,bind_tc_ok,JGg_QueryArrays.state5,bind_tc_ok]
  rw [read6,bind_tc_ok,JGg_QueryArrays.b_update6,bind_tc_ok,advance6,bind_tc_ok,JGg_QueryArrays.a_update6,bind_tc_ok,JGg_QueryArrays.state6,bind_tc_ok]
  rw [read7,bind_tc_ok,JGg_QueryArrays.b_update7,bind_tc_ok,advance7,bind_tc_ok,JGg_QueryArrays.a_update7,bind_tc_ok,JGg_QueryArrays.state7,bind_tc_ok]
  have selectedDecode : Query31ConcreteMaterializedSchedule.actualConcreteDecode
      Query31ConcreteDriverTraceFacts.sourceDefaultState JGg_QueryArrays.b8 JGg_QueryArrays.a8=
      ok (.Ok (q,encodeState JGg_Opening31.next2)) := by
    rw [JGg_QueryArrays.blocks,JGg_QueryArrays.advances]
    exact decode
  change (do
    let r ← Query31ConcreteMaterializedSchedule.actualConcreteDecode
      Query31ConcreteDriverTraceFacts.sourceDefaultState JGg_QueryArrays.b8 JGg_QueryArrays.a8
    _) = _
  rw [selectedDecode,bind_tc_ok]
  simp only [core.result.Result.map_err,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,Aeneas.Std.uncurry]
end AspisR1.JGg_QueryCalls
