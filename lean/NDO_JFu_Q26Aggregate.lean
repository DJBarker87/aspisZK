import NDO_JFu_Q26Window00
import NDO_JFu_Q26Window08
set_option autoImplicit false
namespace AspisR1.JFu_Q26Absorb
open JFp_SHA256
theorem lenB00 : B00.input.length=64 := by rfl
#print axioms lenB00
theorem lenB01 : B01.input.length=64 := by rfl
#print axioms lenB01
theorem lenB02 : B02.input.length=64 := by rfl
#print axioms lenB02
theorem lenB03 : B03.input.length=64 := by rfl
#print axioms lenB03
theorem lenB04 : B04.input.length=64 := by rfl
#print axioms lenB04
theorem lenB05 : B05.input.length=64 := by rfl
#print axioms lenB05
theorem lenB06 : B06.input.length=64 := by rfl
#print axioms lenB06
theorem lenB07 : B07.input.length=64 := by rfl
#print axioms lenB07
theorem lenB08 : B08.input.length=64 := by rfl
#print axioms lenB08
theorem lenB09 : B09.input.length=64 := by rfl
#print axioms lenB09
theorem lenB10 : B10.input.length=64 := by rfl
#print axioms lenB10
theorem lenB11 : B11.input.length=64 := by rfl
#print axioms lenB11
theorem lenB12 : B12.input.length=64 := by rfl
#print axioms lenB12
theorem lenB13 : B13.input.length=64 := by rfl
#print axioms lenB13
theorem lenB14 : B14.input.length=64 := by rfl
#print axioms lenB14
theorem lenB15 : B15.input.length=64 := by rfl
#print axioms lenB15
def head : List (List Nat) := [B00.input,B01.input,B02.input,B03.input,B04.input,B05.input,B06.input,B07.input,B08.input,B09.input,B10.input,B11.input,B12.input,B13.input,B14.input]
def tail : List Nat := [0,0,0,0,0,0,0]
def message : List Nat := head.flatten ++ tail
def chunks : List (List Nat) := head ++ [B15.input]
theorem tailLength : tail.length=7 := by rfl
#print axioms tailLength
theorem headLength : head.flatten.length=960 := by
  simp only [head,List.length_flatten,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,lenB00,lenB01,lenB02,lenB03,lenB04,lenB05,lenB06,lenB07,lenB08,lenB09,lenB10,lenB11,lenB12,lenB13,lenB14]
  omega
#print axioms headLength
theorem messageLength : message.length=967 := by
  simp only [message,List.length_append,headLength,tailLength]
#print axioms messageLength
theorem tailPad : tail ++ [128] ++ List.replicate 48 0 ++ [0,0,0,0,0,0,30,56] = [B15.input].flatten := by rfl
#print axioms tailPad
theorem padded : pad message=chunks.flatten := by
  rw [pad,messageLength]
  change (head.flatten ++ tail) ++ [128] ++ List.replicate 48 0 ++ [0,0,0,0,0,0,30,56]=_
  simp only [List.append_assoc,chunks,List.flatten_append]
  exact congrArg (fun t => head.flatten ++ t) (by simpa only [List.append_assoc] using tailPad)
#print axioms padded
theorem lengths : ∀ c ∈ chunks,c.length=64 := by
  intro c hc
  simp only [chunks,head,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hc
  rcases hc with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
#print axioms lengths
theorem paddedLength : (pad message).length=1024 := by
  rw [padded]
  simp only [chunks,head,List.flatten_append,List.flatten_cons,List.flatten_nil,List.length_append,List.length_nil,List.length_flatten,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,lenB00,lenB01,lenB02,lenB03,lenB04,lenB05,lenB06,lenB07,lenB08,lenB09,lenB10,lenB11,lenB12,lenB13,lenB14,lenB15]
#print axioms paddedLength
theorem blockList : blocks ((pad message).length/64) (pad message)=chunks := by
  rw [paddedLength,padded]
  exact blocks_chunks chunks lengths
#print axioms blockList
def result : Reg := B15.result
theorem checked : JFp_SHA256.hash message=result := by
  unfold JFp_SHA256.hash
  dsimp only
  rw [blockList]
  simp only [chunks,head,List.foldl_append,List.foldl_cons,List.foldl_nil]
  rw [show initial=B00.start from rfl,B00.checked]
  rw [show B00.result=B01.start from rfl,B01.checked]
  rw [show B01.result=B02.start from rfl,B02.checked]
  rw [show B02.result=B03.start from rfl,B03.checked]
  rw [show B03.result=B04.start from rfl,B04.checked]
  rw [show B04.result=B05.start from rfl,B05.checked]
  rw [show B05.result=B06.start from rfl,B06.checked]
  rw [show B06.result=B07.start from rfl,B07.checked]
  rw [show B07.result=B08.start from rfl,B08.checked]
  rw [show B08.result=B09.start from rfl,B09.checked]
  rw [show B09.result=B10.start from rfl,B10.checked]
  rw [show B10.result=B11.start from rfl,B11.checked]
  rw [show B11.result=B12.start from rfl,B12.checked]
  rw [show B12.result=B13.start from rfl,B13.checked]
  rw [show B13.result=B14.start from rfl,B14.checked]
  rw [show B14.result=B15.start from rfl,B15.checked]
  rfl
#print axioms checked
end AspisR1.JFu_Q26Absorb

