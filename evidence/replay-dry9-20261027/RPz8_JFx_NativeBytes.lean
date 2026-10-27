import RPz8_JFx_DataProof00
import RPz8_JFx_DataProof01
import RPz8_JFx_DataProof02
import RPz8_JFx_DataProof03
import RPz8_JFx_DataProof04
import RPz8_JFx_DataProof05
import RPz8_JFx_DataProof06
import RPz8_JFx_DataProof07
import RPz8_JFx_DataProof08
import RPz8_JFx_DataProof09
import RPz8_JFx_DataProof10
import RPz8_JFx_DataProof11
import RPz8_JFx_DataProof12
import RPz8_JFx_DataProof13
import RPz8_JFx_DataProof14
import RPz8_JFx_DataPublic00
import RPz8_JFx_DataCheckpoint00
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFx_NativeBytes
open Aeneas Aeneas.Std
def proofBytes : List U8 := JFx_DataProof00.bytes ++ JFx_DataProof01.bytes ++ JFx_DataProof02.bytes ++ JFx_DataProof03.bytes ++ JFx_DataProof04.bytes ++ JFx_DataProof05.bytes ++ JFx_DataProof06.bytes ++ JFx_DataProof07.bytes ++ JFx_DataProof08.bytes ++ JFx_DataProof09.bytes ++ JFx_DataProof10.bytes ++ JFx_DataProof11.bytes ++ JFx_DataProof12.bytes ++ JFx_DataProof13.bytes ++ JFx_DataProof14.bytes
theorem proofBytes_length : proofBytes.length = 57607 := by
  simp only [proofBytes,List.length_append,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length]
#print axioms proofBytes_length
def proof : Slice U8 := ⟨proofBytes,by rw [proofBytes_length]; scalar_tac⟩
def publicBytes : List U8 := JFx_DataPublic00.bytes
theorem publicBytes_length : publicBytes.length = 1880 := by
  simp only [publicBytes,JFx_DataPublic00.length]
#print axioms publicBytes_length
def publicInput : Slice U8 := ⟨publicBytes,by rw [publicBytes_length]; scalar_tac⟩
def checkpointBytes : List U8 := JFx_DataCheckpoint00.bytes
theorem checkpointBytes_length : checkpointBytes.length = 1768 := by
  simp only [checkpointBytes,JFx_DataCheckpoint00.length]
#print axioms checkpointBytes_length
def checkpoint : Slice U8 := ⟨checkpointBytes,by rw [checkpointBytes_length]; scalar_tac⟩
end AspisR1.JFx_NativeBytes
end
