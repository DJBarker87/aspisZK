import NDO_JGz_SHAC00
import NDO_JGz_SHAC01
import NDO_JGz_SHAC0Fold
import NDO_JGz_ChecksumNative
import NDO_JGz_HashTools
set_option autoImplicit false
namespace AspisR1.JGz_ChecksumSHA
open JFp_SHA256
def head : List (List Nat) := JGz_SHAC00.chunks ++ [JGz_SHAC01.B016.input,JGz_SHAC01.B017.input,JGz_SHAC01.B018.input,JGz_SHAC01.B019.input,JGz_SHAC01.B020.input,JGz_SHAC01.B021.input,JGz_SHAC01.B022.input,JGz_SHAC01.B023.input,JGz_SHAC01.B024.input,JGz_SHAC01.B025.input,JGz_SHAC01.B026.input]
def chunks : List (List Nat) := JGz_SHAC00.chunks ++ JGz_SHAC01.chunks
def raw : List Nat := head.flatten ++ JGz_ChecksumNative.tail
theorem headLength : head.length=27 := by rfl
#print axioms headLength
theorem tailLength : JGz_ChecksumNative.tail.length=30 := by rfl
#print axioms tailLength
theorem headLengths : ∀ b ∈ head,b.length=64 := by
  intro b hb
  simp only [head,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11
  · exact JGz_SHAC0Fold.lengths b h0
  · subst b;rfl
  · subst b;rfl
  · subst b;rfl
  · subst b;rfl
  · subst b;rfl
  · subst b;rfl
  · subst b;rfl
  · subst b;rfl
  · subst b;rfl
  · subst b;rfl
  · subst b;rfl
#print axioms headLengths
theorem rawLength : raw.length=1758 := by
  simp only [raw,List.length_append,JGz_HashTools.length_flatten head headLengths,headLength,tailLength]
#print axioms rawLength
theorem tailPad : JGz_ChecksumNative.tail ++ [128] ++ List.replicate 25 0 ++ [0,0,0,0,0,0,54,240]=JGz_SHAC01.B027.input := by rfl
#print axioms tailPad
theorem padded : pad raw=chunks.flatten := by
  rw [pad,rawLength]
  change (head.flatten ++ JGz_ChecksumNative.tail) ++ [128] ++ List.replicate 25 0 ++ [0,0,0,0,0,0,54,240]=_
  simp only [List.append_assoc]
  rw [show JGz_ChecksumNative.tail ++ ([128] ++ (List.replicate 25 0 ++ [0,0,0,0,0,0,54,240]))=JGz_SHAC01.B027.input from by simpa only [List.append_assoc] using tailPad]
  simp only [head,chunks,JGz_SHAC01.chunks,List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms padded
theorem lengths : ∀ b ∈ chunks,b.length=64 := by
  intro b hb
  simp only [chunks,List.mem_append] at hb
  rcases hb with h0|h1
  · exact JGz_SHAC0Fold.lengths b h0
  · exact JGz_SHAC01.lengths b h1
#print axioms lengths
theorem checked : JFp_SHA256.hash raw=JGz_SHAC01.B027.result := by
  rw [JGz_HashTools.hash_chunks raw chunks padded lengths]
  unfold chunks
  simp only [List.foldl_append]
  rw [show initial=JGz_SHAC00.B000.start from rfl]
  rw [JGz_SHAC0Fold.folded]
  rw [show JGz_SHAC00.B015.result=JGz_SHAC01.B016.start from rfl]
  rw [JGz_SHAC01.folded]
#print axioms checked
end AspisR1.JGz_ChecksumSHA
