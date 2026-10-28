import NDO_JGe_Q31Absorb
import NDO_JGe_Q31Read0
import NDO_JGe_Q31Ratchet0
import NDO_JGe_Q31Read1
import NDO_JGe_Q31Ratchet1
import NDO_JGe_Q31Read2
import NDO_JGe_Q31Ratchet2
import NDO_JGe_Q31Read3
import NDO_JGe_Q31Ratchet3
import NDO_JGe_Q31Read4
import NDO_JGe_Q31Ratchet4
import NDO_JGe_Q31Read5
import NDO_JGe_Q31Ratchet5
import NDO_JGe_Q31Read6
import NDO_JGe_Q31Ratchet6
import NDO_JGe_Q31Read7
import NDO_JGe_Q31Ratchet7
import NDO_JGe_OpeningInit
import RPz7_F3J_QueryPairs
import NDO_JGg_Input31
set_option autoImplicit false
namespace AspisR1.JGg_Opening31
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
def before : State := JGg_Input31.before
def payload : Slice U8 := JGg_Input31.payload
def absorbed : State := JFp_SHADigest.output JGe_Q31Absorb.result
def block0 : State := JFp_SHADigest.output JGe_Q31Read0.result
def next0 : State := JFp_SHADigest.output JGe_Q31Ratchet0.result
def block1 : State := JFp_SHADigest.output JGe_Q31Read1.result
def next1 : State := JFp_SHADigest.output JGe_Q31Ratchet1.result
def block2 : State := JFp_SHADigest.output JGe_Q31Read2.result
def next2 : State := JFp_SHADigest.output JGe_Q31Ratchet2.result
def block3 : State := JFp_SHADigest.output JGe_Q31Read3.result
def next3 : State := JFp_SHADigest.output JGe_Q31Ratchet3.result
def block4 : State := JFp_SHADigest.output JGe_Q31Read4.result
def next4 : State := JFp_SHADigest.output JGe_Q31Ratchet4.result
def block5 : State := JFp_SHADigest.output JGe_Q31Read5.result
def next5 : State := JFp_SHADigest.output JGe_Q31Ratchet5.result
def block6 : State := JFp_SHADigest.output JGe_Q31Read6.result
def next6 : State := JFp_SHADigest.output JGe_Q31Ratchet6.result
def block7 : State := JFp_SHADigest.output JGe_Q31Read7.result
def next7 : State := JFp_SHADigest.output JGe_Q31Ratchet7.result
theorem absorbInput : (flatten (CallerStep.openingAbsorbParts (encodeState before) 191#u8 2048#u32 payload)).map Fin.val=JGe_Q31Absorb.message := JGg_Input31.native
#print axioms absorbInput
theorem absorbHash : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (CallerStep.openingAbsorbParts (encodeState before) 191#u8 2048#u32 payload)=encodeState absorbed := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [absorbInput,JGe_Q31Absorb.checked]
  rfl
#print axioms absorbHash
theorem readInput0 : (flatten (TranscriptStep.readParts (encodeState absorbed) 1#u8)).map Fin.val=JGe_Q31Read0.message := by rfl
#print axioms readInput0
theorem readHash0 : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState absorbed) 1#u8)=encodeState block0 := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [readInput0,JGe_Q31Read0.checked]
  rfl
#print axioms readHash0
theorem advanceInput0 : (flatten (TranscriptStep.readParts (encodeState absorbed) 2#u8)).map Fin.val=JGe_Q31Ratchet0.message := by rfl
#print axioms advanceInput0
theorem advanceHash0 : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState absorbed) 2#u8)=encodeState next0 := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [advanceInput0,JGe_Q31Ratchet0.checked]
  rfl
#print axioms advanceHash0
theorem readInput1 : (flatten (TranscriptStep.readParts (encodeState next0) 1#u8)).map Fin.val=JGe_Q31Read1.message := by rfl
#print axioms readInput1
theorem readHash1 : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState next0) 1#u8)=encodeState block1 := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [readInput1,JGe_Q31Read1.checked]
  rfl
#print axioms readHash1
theorem advanceInput1 : (flatten (TranscriptStep.readParts (encodeState next0) 2#u8)).map Fin.val=JGe_Q31Ratchet1.message := by rfl
#print axioms advanceInput1
theorem advanceHash1 : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState next0) 2#u8)=encodeState next1 := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [advanceInput1,JGe_Q31Ratchet1.checked]
  rfl
#print axioms advanceHash1
theorem readInput2 : (flatten (TranscriptStep.readParts (encodeState next1) 1#u8)).map Fin.val=JGe_Q31Read2.message := by rfl
#print axioms readInput2
theorem readHash2 : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState next1) 1#u8)=encodeState block2 := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [readInput2,JGe_Q31Read2.checked]
  rfl
#print axioms readHash2
theorem advanceInput2 : (flatten (TranscriptStep.readParts (encodeState next1) 2#u8)).map Fin.val=JGe_Q31Ratchet2.message := by rfl
#print axioms advanceInput2
theorem advanceHash2 : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState next1) 2#u8)=encodeState next2 := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [advanceInput2,JGe_Q31Ratchet2.checked]
  rfl
#print axioms advanceHash2
theorem readInput3 : (flatten (TranscriptStep.readParts (encodeState next2) 1#u8)).map Fin.val=JGe_Q31Read3.message := by rfl
#print axioms readInput3
theorem readHash3 : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState next2) 1#u8)=encodeState block3 := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [readInput3,JGe_Q31Read3.checked]
  rfl
#print axioms readHash3
theorem advanceInput3 : (flatten (TranscriptStep.readParts (encodeState next2) 2#u8)).map Fin.val=JGe_Q31Ratchet3.message := by rfl
#print axioms advanceInput3
theorem advanceHash3 : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState next2) 2#u8)=encodeState next3 := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [advanceInput3,JGe_Q31Ratchet3.checked]
  rfl
#print axioms advanceHash3
theorem readInput4 : (flatten (TranscriptStep.readParts (encodeState next3) 1#u8)).map Fin.val=JGe_Q31Read4.message := by rfl
#print axioms readInput4
theorem readHash4 : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState next3) 1#u8)=encodeState block4 := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [readInput4,JGe_Q31Read4.checked]
  rfl
#print axioms readHash4
theorem advanceInput4 : (flatten (TranscriptStep.readParts (encodeState next3) 2#u8)).map Fin.val=JGe_Q31Ratchet4.message := by rfl
#print axioms advanceInput4
theorem advanceHash4 : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState next3) 2#u8)=encodeState next4 := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [advanceInput4,JGe_Q31Ratchet4.checked]
  rfl
#print axioms advanceHash4
theorem readInput5 : (flatten (TranscriptStep.readParts (encodeState next4) 1#u8)).map Fin.val=JGe_Q31Read5.message := by rfl
#print axioms readInput5
theorem readHash5 : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState next4) 1#u8)=encodeState block5 := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [readInput5,JGe_Q31Read5.checked]
  rfl
#print axioms readHash5
theorem advanceInput5 : (flatten (TranscriptStep.readParts (encodeState next4) 2#u8)).map Fin.val=JGe_Q31Ratchet5.message := by rfl
#print axioms advanceInput5
theorem advanceHash5 : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState next4) 2#u8)=encodeState next5 := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [advanceInput5,JGe_Q31Ratchet5.checked]
  rfl
#print axioms advanceHash5
theorem readInput6 : (flatten (TranscriptStep.readParts (encodeState next5) 1#u8)).map Fin.val=JGe_Q31Read6.message := by rfl
#print axioms readInput6
theorem readHash6 : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState next5) 1#u8)=encodeState block6 := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [readInput6,JGe_Q31Read6.checked]
  rfl
#print axioms readHash6
theorem advanceInput6 : (flatten (TranscriptStep.readParts (encodeState next5) 2#u8)).map Fin.val=JGe_Q31Ratchet6.message := by rfl
#print axioms advanceInput6
theorem advanceHash6 : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState next5) 2#u8)=encodeState next6 := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [advanceInput6,JGe_Q31Ratchet6.checked]
  rfl
#print axioms advanceHash6
theorem readInput7 : (flatten (TranscriptStep.readParts (encodeState next6) 1#u8)).map Fin.val=JGe_Q31Read7.message := by rfl
#print axioms readInput7
theorem readHash7 : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState next6) 1#u8)=encodeState block7 := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [readInput7,JGe_Q31Read7.checked]
  rfl
#print axioms readHash7
theorem advanceInput7 : (flatten (TranscriptStep.readParts (encodeState next6) 2#u8)).map Fin.val=JGe_Q31Ratchet7.message := by rfl
#print axioms advanceInput7
theorem advanceHash7 : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState next6) 2#u8)=encodeState next7 := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [advanceInput7,JGe_Q31Ratchet7.checked]
  rfl
#print axioms advanceHash7
theorem length : payload.length=2048 := JGe_Payload31.length
#print axioms length
attribute [local irreducible] payload before absorbed
theorem absorb {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    transcript.Transcript.absorb D0 (⟨encodeState before,hash⟩ : transcript.Transcript Hash) 31#u8 payload=ok (⟨encodeState absorbed,hash⟩ : transcript.Transcript Hash) := by
  dsimp only
  have len : Slice.len payload=2048#usize := by
    apply UScalar.eq_of_val_eq
    exact length
  have cast : UScalar.cast .U32 (Slice.len payload)=2048#u32 := by rw [len];scalar_tac
  rw [CallerStep.opening_absorb_eq _ _ 31#u8 191#u8 payload 2048#u32 (by rfl) cast]
  change (do let s ← ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
             (CallerStep.openingAbsorbParts (encodeState before) 191#u8 2048#u32 payload))
             ok (⟨s,hash⟩ : transcript.Transcript Hash))=_
  rw [absorbHash,bind_tc_ok]
#print axioms absorb
theorem pairs {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    ∃ calls,F3J_QueryPairs.Pairs D0 hash 8 (encodeState absorbed) calls := by
  dsimp only
  refine ⟨[(TranscriptStep.readParts (encodeState absorbed) 1#u8,encodeState block0),(TranscriptStep.readParts (encodeState absorbed) 2#u8,encodeState next0),(TranscriptStep.readParts (encodeState next0) 1#u8,encodeState block1),(TranscriptStep.readParts (encodeState next0) 2#u8,encodeState next1),(TranscriptStep.readParts (encodeState next1) 1#u8,encodeState block2),(TranscriptStep.readParts (encodeState next1) 2#u8,encodeState next2),(TranscriptStep.readParts (encodeState next2) 1#u8,encodeState block3),(TranscriptStep.readParts (encodeState next2) 2#u8,encodeState next3),(TranscriptStep.readParts (encodeState next3) 1#u8,encodeState block4),(TranscriptStep.readParts (encodeState next3) 2#u8,encodeState next4),(TranscriptStep.readParts (encodeState next4) 1#u8,encodeState block5),(TranscriptStep.readParts (encodeState next4) 2#u8,encodeState next5),(TranscriptStep.readParts (encodeState next5) 1#u8,encodeState block6),(TranscriptStep.readParts (encodeState next5) 2#u8,encodeState next6),(TranscriptStep.readParts (encodeState next6) 1#u8,encodeState block7),(TranscriptStep.readParts (encodeState next6) 2#u8,encodeState next7)],?_⟩
  apply F3J_QueryPairs.Pairs.cons
  · change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=ok (encodeState block0)
    rw [readHash0]
  · change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=ok (encodeState next0)
    rw [advanceHash0]
  apply F3J_QueryPairs.Pairs.cons
  · change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=ok (encodeState block1)
    rw [readHash1]
  · change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=ok (encodeState next1)
    rw [advanceHash1]
  apply F3J_QueryPairs.Pairs.cons
  · change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=ok (encodeState block2)
    rw [readHash2]
  · change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=ok (encodeState next2)
    rw [advanceHash2]
  apply F3J_QueryPairs.Pairs.cons
  · change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=ok (encodeState block3)
    rw [readHash3]
  · change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=ok (encodeState next3)
    rw [advanceHash3]
  apply F3J_QueryPairs.Pairs.cons
  · change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=ok (encodeState block4)
    rw [readHash4]
  · change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=ok (encodeState next4)
    rw [advanceHash4]
  apply F3J_QueryPairs.Pairs.cons
  · change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=ok (encodeState block5)
    rw [readHash5]
  · change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=ok (encodeState next5)
    rw [advanceHash5]
  apply F3J_QueryPairs.Pairs.cons
  · change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=ok (encodeState block6)
    rw [readHash6]
  · change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=ok (encodeState next6)
    rw [advanceHash6]
  apply F3J_QueryPairs.Pairs.cons
  · change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=ok (encodeState block7)
    rw [readHash7]
  · change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=ok (encodeState next7)
    rw [advanceHash7]
  exact .nil _
#print axioms pairs
end AspisR1.JGg_Opening31
