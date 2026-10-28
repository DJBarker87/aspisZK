import NDO_JGe_Q32Absorb
import NDO_JGe_Q32Read0
import NDO_JGe_Q32Ratchet0
import NDO_JGe_OpeningInit
import RPz7_F3J_QueryPairs
import NDO_JGe_Q31Ratchet2
set_option autoImplicit false
namespace AspisR1.JGg_Opening32
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
def before : State := JFp_SHADigest.output JGe_Q31Ratchet2.result
def payload : Slice U8 := ⟨[],by simp⟩
def absorbed : State := JFp_SHADigest.output JGe_Q32Absorb.result
def block0 : State := JFp_SHADigest.output JGe_Q32Read0.result
def next0 : State := JFp_SHADigest.output JGe_Q32Ratchet0.result
theorem absorbInput : (flatten (CallerStep.openingAbsorbParts (encodeState before) 192#u8 0#u32 payload)).map Fin.val=JGe_Q32Absorb.message := by
  have le : (core.num.U32.to_le_bytes 0#u32).val.map (fun x=>x.val)=[0, 0, 0, 0] := by
    simp [core.num.U32.to_le_bytes,BitVec.toLEBytes] <;> (repeat' constructor) <;> scalar_tac
  simp only [flatten,CallerStep.openingAbsorbParts,Array.to_slice,Array.make,List.flatMap_cons,List.flatMap_nil,List.map_append,List.append_nil,List.map_map,Function.comp_def,decodeByte,List.map_cons,List.map_nil]
  rw [le]
  rfl
#print axioms absorbInput
theorem absorbHash : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (CallerStep.openingAbsorbParts (encodeState before) 192#u8 0#u32 payload)=encodeState absorbed := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [absorbInput,JGe_Q32Absorb.checked]
  rfl
#print axioms absorbHash
theorem readInput0 : (flatten (TranscriptStep.readParts (encodeState absorbed) 1#u8)).map Fin.val=JGe_Q32Read0.message := by rfl
#print axioms readInput0
theorem readHash0 : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState absorbed) 1#u8)=encodeState block0 := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [readInput0,JGe_Q32Read0.checked]
  rfl
#print axioms readHash0
theorem advanceInput0 : (flatten (TranscriptStep.readParts (encodeState absorbed) 2#u8)).map Fin.val=JGe_Q32Ratchet0.message := by rfl
#print axioms advanceInput0
theorem advanceHash0 : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState absorbed) 2#u8)=encodeState next0 := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [advanceInput0,JGe_Q32Ratchet0.checked]
  rfl
#print axioms advanceHash0
theorem length : payload.length=0 := by simp only [payload,Slice.length,List.length_replicate,List.length_nil]
#print axioms length
attribute [local irreducible] payload before absorbed
theorem absorb {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    transcript.Transcript.absorb D0 (⟨encodeState before,hash⟩ : transcript.Transcript Hash) 32#u8 payload=ok (⟨encodeState absorbed,hash⟩ : transcript.Transcript Hash) := by
  dsimp only
  have len : Slice.len payload=0#usize := by
    apply UScalar.eq_of_val_eq
    exact length
  have cast : UScalar.cast .U32 (Slice.len payload)=0#u32 := by rw [len];scalar_tac
  rw [CallerStep.opening_absorb_eq _ _ 32#u8 192#u8 payload 0#u32 (by rfl) cast]
  change (do let s ← ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
             (CallerStep.openingAbsorbParts (encodeState before) 192#u8 0#u32 payload))
             ok (⟨s,hash⟩ : transcript.Transcript Hash))=_
  rw [absorbHash,bind_tc_ok]
#print axioms absorb
theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    transcript.Transcript.block D0 (⟨encodeState before,hash⟩ : transcript.Transcript Hash) 32#u8 payload=ok (encodeState block0,(⟨encodeState next0,hash⟩ : transcript.Transcript Hash)) := by
  dsimp only
  rw [transcript.Transcript.block,absorb]
  simp only [bind_tc_ok,lift]
  change (do let b ← ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState absorbed) 1#u8))
             let s ← ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState absorbed) 2#u8))
             ok (b,(⟨s,hash⟩ : transcript.Transcript Hash)))=_
  rw [readHash0,bind_tc_ok,advanceHash0,bind_tc_ok]
#print axioms source
end AspisR1.JGg_Opening32
