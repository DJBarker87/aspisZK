import NDO_JGe_InitBlocks00
import NDO_JFp_SeedHash
set_option autoImplicit false
namespace AspisR1.JGe_Init
open JFp_SHA256 JFp_SeedHash
def message : List Nat := [85,78,80,82,79,86,69,68,58,82,49,58,80,82,73,86,65,84,69,45,83,65,76,84,69,68,58,80,51,2,153,53,65,222,28,230,28,153,224,232,175,71,74,113,170,81,95,211,179,206,232,161,251,132,103,67,200,127,106,176,33,169]
def chunks : List (List Nat) := [B00.input,B01.input]
theorem padded : pad message=chunks.flatten := by rfl
#print axioms padded
theorem lenB00 : B00.input.length=64 := by rfl
#print axioms lenB00
theorem lenB01 : B01.input.length=64 := by rfl
#print axioms lenB01
theorem lengths : ∀ c∈chunks,c.length=64 := by
  intro c hc
  simp only [chunks,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h0 | h1
  · subst c;exact lenB00
  · subst c;exact lenB01
#print axioms lengths
theorem paddedLength : (pad message).length=128 := by
  rw [padded]
  simp only [chunks,List.flatten_cons,List.flatten_nil,List.length_append,List.length_nil,lenB00,lenB01]
#print axioms paddedLength
theorem blockList : blocks ((pad message).length/64) (pad message)=chunks := by
  rw [paddedLength,padded]
  exact blocks_chunks chunks lengths
#print axioms blockList
def result : Reg := B01.result
theorem checked : JFp_SHA256.hash message=result := by
  unfold JFp_SHA256.hash
  dsimp only
  rw [blockList]
  simp only [chunks,List.foldl_cons,List.foldl_nil]
  rw [show initial=B00.start from rfl,B00.checked]
  rw [show B00.result=B01.start from rfl,B01.checked]
  rfl
#print axioms checked
end AspisR1.JGe_Init
