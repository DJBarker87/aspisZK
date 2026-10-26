import JFw_ChunkDecode
import MultiproofConeByteEquality
set_option autoImplicit false
namespace AspisR1.JFw_Blocks
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical
open MultiproofConeCanonicalAppend MultiproofConeExpandModel

def blocks : Nat → List U8 → List (List U8)
  | 0,_ => []
  | n+1,b => (b.take 16 ++ List.replicate 16 0#u8) :: blocks n (b.drop 16)

theorem bytes (n : Nat) (b : List U8) :
    bytesOf (blocks n b).flatten = expand n (bytesOf b) := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    rw [expand_step]
    have zeroByte : AspisV8R19.SqueezeOracleBridge.decodeByte 0#u8 = 0 := rfl
    simp only [blocks,List.flatten_cons,bytes_append,bytesOf,List.map_append,List.map_replicate,zeroByte,
      ← List.map_take,← List.map_drop]
    simpa only [bytesOf,List.map_take] using
      congrArg (fun tail => ((bytesOf b).take 16 ++ List.replicate 16 0) ++ tail) (ih (b.drop 16))

theorem valid (n : Nat) (b : List U8) (length : b.length = 16*n)
    (canon : canonical (bytesOf b)) :
    ∀ chunk ∈ blocks n b, chunk.length = 32 ∧ canonical (bytesOf chunk) ∧
      chunk.drop 16 = List.replicate 16 0#u8 := by
  induction n generalizing b with
  | zero => simp only [blocks,List.not_mem_nil,false_implies,implies_true]
  | succ n ih =>
    have zeroByte : AspisV8R19.SqueezeOracleBridge.decodeByte 0#u8 = 0 := rfl
    have enough : 16 ≤ b.length := by omega
    have firstLength : (b.take 16).length = 16 := by simp only [List.length_take];omega
    have pair := (canonical_take_drop (bytesOf b) 16 (by decide)
      (by simp only [bytesOf,List.length_map];exact enough)).mp canon
    have firstCanon : canonical (bytesOf (b.take 16)) := by
      simpa only [bytesOf,List.map_take] using pair.1
    have restCanon : canonical (bytesOf (b.drop 16)) := by
      simpa only [bytesOf,List.map_drop] using pair.2
    intro chunk mem
    rcases List.mem_cons.mp mem with rfl | later
    · refine ⟨by simp only [List.length_append,firstLength,List.length_replicate],?_,?_⟩
      · rw [bytes_append,canonical_append _ _ firstCanon.1]
        exact ⟨firstCanon,by simpa only [bytesOf,List.map_replicate,zeroByte] using
          PSem_Canonical.canonical_zeros 16 (by decide)⟩
      · rw [List.drop_append,firstLength,Nat.sub_self,List.drop_zero,
          List.drop_eq_nil_of_le (by omega : (b.take 16).length ≤ 16),List.nil_append]
    · exact ih (b.drop 16) (by rw [List.length_drop];omega) restCanon chunk later

#print axioms bytes
#print axioms valid
end AspisR1.JFw_Blocks
