import NDO_JGz_SHAU00
import NDO_JGz_SHAU01
import NDO_JGz_PublicNative
import NDO_JGz_HashTools
set_option autoImplicit false
namespace AspisR1.JGz_PublicSHA
open JFp_SHA256
def head : List (List Nat) := JGz_SHAU00.chunks ++ [JGz_SHAU01.B016.input,JGz_SHAU01.B017.input,JGz_SHAU01.B018.input,JGz_SHAU01.B019.input,JGz_SHAU01.B020.input,JGz_SHAU01.B021.input,JGz_SHAU01.B022.input,JGz_SHAU01.B023.input,JGz_SHAU01.B024.input,JGz_SHAU01.B025.input,JGz_SHAU01.B026.input,JGz_SHAU01.B027.input,JGz_SHAU01.B028.input]
def chunks : List (List Nat) := JGz_SHAU00.chunks ++ JGz_SHAU01.chunks
def raw : List Nat := head.flatten ++ JGz_PublicNative.tail
theorem headLength : head.length=29 := by rfl
#print axioms headLength
theorem tailLength : JGz_PublicNative.tail.length=24 := by rfl
#print axioms tailLength
theorem headLengths : ∀ b ∈ head,b.length=64 := by
  intro b hb
  simp only [head,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13
  · exact JGz_SHAU00.lengths b h0
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
  · subst b;rfl
  · subst b;rfl
#print axioms headLengths
theorem rawLength : raw.length=1880 := by
  simp only [raw,List.length_append,JGz_HashTools.length_flatten head headLengths,headLength,tailLength]
#print axioms rawLength
theorem tailPad : JGz_PublicNative.tail ++ [128] ++ List.replicate 31 0 ++ [0,0,0,0,0,0,58,192]=JGz_SHAU01.B029.input := by rfl
#print axioms tailPad
theorem padded : pad raw=chunks.flatten := by
  rw [pad,rawLength]
  change (head.flatten ++ JGz_PublicNative.tail) ++ [128] ++ List.replicate 31 0 ++ [0,0,0,0,0,0,58,192]=_
  simp only [List.append_assoc]
  rw [show JGz_PublicNative.tail ++ ([128] ++ (List.replicate 31 0 ++ [0,0,0,0,0,0,58,192]))=JGz_SHAU01.B029.input from by simpa only [List.append_assoc] using tailPad]
  simp only [head,chunks,JGz_SHAU01.chunks,List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms padded
theorem lengths : ∀ b ∈ chunks,b.length=64 := by
  intro b hb
  simp only [chunks,List.mem_append] at hb
  rcases hb with h0|h1
  · exact JGz_SHAU00.lengths b h0
  · exact JGz_SHAU01.lengths b h1
#print axioms lengths
theorem checked : JFp_SHA256.hash raw=JGz_SHAU01.B029.result := by
  rw [JGz_HashTools.hash_chunks raw chunks padded lengths]
  unfold chunks
  simp only [List.foldl_append]
  rw [show initial=JGz_SHAU00.B000.start from rfl]
  rw [JGz_SHAU00.folded]
  rw [show JGz_SHAU00.B015.result=JGz_SHAU01.B016.start from rfl]
  rw [JGz_SHAU01.folded]
#print axioms checked
end AspisR1.JGz_PublicSHA
