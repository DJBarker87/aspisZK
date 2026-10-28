import NDO_JFp_SHABlock00
import NDO_JFp_SHABlock01
import NDO_JFp_SHABlock02
import NDO_JFp_SHABlock03
import NDO_JFp_SHABlock04
import NDO_JFp_SHABlock05
import NDO_JFp_SHABlock06
import NDO_JFp_SHABlock07
import NDO_JFp_SHABlock08
import NDO_JFp_SHABlock09
import NDO_JFp_SHABlock10
import NDO_JFp_SHABlock11
import NDO_JFp_SHABlock12
import NDO_JFp_SHABlock13
import NDO_JFp_SHABlock14
import NDO_JFp_SHABlock15
import NDO_JFp_SHABlock16
import NDO_JFp_SHABlock17
import NDO_JFp_SHABlock18
import NDO_JFp_SHABlock19
import NDO_JFp_SHABlock20
import NDO_JFp_SHABlock21
import NDO_JFp_SHABlock22
import NDO_JFp_SHABlock23
import NDO_JFp_SHABlock24
import NDO_JFp_SHABlocks
set_option autoImplicit false
namespace AspisR1.JFp_SeedHash
open JFp_SHA256
theorem len00 : JFp_SHABlock00.input.length=64 := by rfl
#print axioms len00
theorem len01 : JFp_SHABlock01.input.length=64 := by rfl
#print axioms len01
theorem len02 : JFp_SHABlock02.input.length=64 := by rfl
#print axioms len02
theorem len03 : JFp_SHABlock03.input.length=64 := by rfl
#print axioms len03
theorem len04 : JFp_SHABlock04.input.length=64 := by rfl
#print axioms len04
theorem len05 : JFp_SHABlock05.input.length=64 := by rfl
#print axioms len05
theorem len06 : JFp_SHABlock06.input.length=64 := by rfl
#print axioms len06
theorem len07 : JFp_SHABlock07.input.length=64 := by rfl
#print axioms len07
theorem len08 : JFp_SHABlock08.input.length=64 := by rfl
#print axioms len08
theorem len09 : JFp_SHABlock09.input.length=64 := by rfl
#print axioms len09
theorem len10 : JFp_SHABlock10.input.length=64 := by rfl
#print axioms len10
theorem len11 : JFp_SHABlock11.input.length=64 := by rfl
#print axioms len11
theorem len12 : JFp_SHABlock12.input.length=64 := by rfl
#print axioms len12
theorem len13 : JFp_SHABlock13.input.length=64 := by rfl
#print axioms len13
theorem len14 : JFp_SHABlock14.input.length=64 := by rfl
#print axioms len14
theorem len15 : JFp_SHABlock15.input.length=64 := by rfl
#print axioms len15
theorem len16 : JFp_SHABlock16.input.length=64 := by rfl
#print axioms len16
theorem len17 : JFp_SHABlock17.input.length=64 := by rfl
#print axioms len17
theorem len18 : JFp_SHABlock18.input.length=64 := by rfl
#print axioms len18
theorem len19 : JFp_SHABlock19.input.length=64 := by rfl
#print axioms len19
theorem len20 : JFp_SHABlock20.input.length=64 := by rfl
#print axioms len20
theorem len21 : JFp_SHABlock21.input.length=64 := by rfl
#print axioms len21
theorem len22 : JFp_SHABlock22.input.length=64 := by rfl
#print axioms len22
theorem len23 : JFp_SHABlock23.input.length=64 := by rfl
#print axioms len23
theorem len24 : JFp_SHABlock24.input.length=64 := by rfl
#print axioms len24
def head : List (List Nat) := [JFp_SHABlock00.input,JFp_SHABlock01.input,JFp_SHABlock02.input,JFp_SHABlock03.input,JFp_SHABlock04.input,JFp_SHABlock05.input,JFp_SHABlock06.input,JFp_SHABlock07.input,JFp_SHABlock08.input,JFp_SHABlock09.input,JFp_SHABlock10.input,JFp_SHABlock11.input,JFp_SHABlock12.input,JFp_SHABlock13.input,JFp_SHABlock14.input,JFp_SHABlock15.input,JFp_SHABlock16.input,JFp_SHABlock17.input,JFp_SHABlock18.input,JFp_SHABlock19.input,JFp_SHABlock20.input,JFp_SHABlock21.input,JFp_SHABlock22.input]
def chunks : List (List Nat) := head ++ [JFp_SHABlock23.input,JFp_SHABlock24.input]
def tail : List Nat := [5,78,38,224,4,15,229,231,69,28,172,155,93,123,197,163,23,111,35,173,17,9,211,192,171,39,154,186,129,123,118,141,34,107,41,162,65,31,231,186,247,183,176,78,206,66,178,115,221,182,126,10,44,98,98,19,142,75]
def raw : List Nat := head.flatten ++ tail
theorem tailLength : tail.length=58 := by rfl
#print axioms tailLength
theorem headLength : head.flatten.length=1472 := by
  simp only [head,List.length_flatten,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,len00,len01,len02,len03,len04,len05,len06,len07,len08,len09,len10,len11,len12,len13,len14,len15,len16,len17,len18,len19,len20,len21,len22]
  omega
#print axioms headLength
theorem rawLength : raw.length=1530 := by
  simp only [raw,List.length_append,headLength,tailLength]
#print axioms rawLength
theorem tailPad : tail ++ [128] ++ List.replicate 61 0 ++ [0,0,0,0,0,0,47,208] = JFp_SHABlock23.input ++ JFp_SHABlock24.input := by rfl
#print axioms tailPad
theorem padded : pad raw=chunks.flatten := by
  rw [pad,rawLength]
  change (head.flatten ++ tail) ++ [128] ++ List.replicate 61 0 ++ [0,0,0,0,0,0,47,208]=_
  simp only [List.append_assoc, chunks,List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  exact congrArg (fun t => head.flatten ++ t) (by simpa only [List.append_assoc] using tailPad)
#print axioms padded
theorem chunkLengths : ∀ c ∈ chunks,c.length=64 := by
  intro c hc
  simp only [chunks,head,List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,or_assoc] at hc
  rcases hc with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24
  · subst c;exact len00
  · subst c;exact len01
  · subst c;exact len02
  · subst c;exact len03
  · subst c;exact len04
  · subst c;exact len05
  · subst c;exact len06
  · subst c;exact len07
  · subst c;exact len08
  · subst c;exact len09
  · subst c;exact len10
  · subst c;exact len11
  · subst c;exact len12
  · subst c;exact len13
  · subst c;exact len14
  · subst c;exact len15
  · subst c;exact len16
  · subst c;exact len17
  · subst c;exact len18
  · subst c;exact len19
  · subst c;exact len20
  · subst c;exact len21
  · subst c;exact len22
  · subst c;exact len23
  · subst c;exact len24
#print axioms chunkLengths
theorem paddedLength : (pad raw).length=1600 := by
  rw [padded]
  simp only [chunks,List.flatten_append,List.length_append,headLength,List.flatten_cons,List.flatten_nil,List.length_nil,len23,len24]
#print axioms paddedLength
theorem blockList : blocks ((pad raw).length/64) (pad raw)=chunks := by
  rw [paddedLength,padded]
  exact blocks_chunks chunks chunkLengths
#print axioms blockList
theorem checked : JFp_SHA256.hash raw=JFp_SHABlock24.result := by
  unfold JFp_SHA256.hash
  dsimp only
  rw [blockList]
  simp only [chunks,head,List.foldl_append,List.foldl_cons,List.foldl_nil]
  rw [show initial=JFp_SHABlock00.start from rfl,JFp_SHABlock00.checked]
  rw [show JFp_SHABlock00.result=JFp_SHABlock01.start from rfl,JFp_SHABlock01.checked]
  rw [show JFp_SHABlock01.result=JFp_SHABlock02.start from rfl,JFp_SHABlock02.checked]
  rw [show JFp_SHABlock02.result=JFp_SHABlock03.start from rfl,JFp_SHABlock03.checked]
  rw [show JFp_SHABlock03.result=JFp_SHABlock04.start from rfl,JFp_SHABlock04.checked]
  rw [show JFp_SHABlock04.result=JFp_SHABlock05.start from rfl,JFp_SHABlock05.checked]
  rw [show JFp_SHABlock05.result=JFp_SHABlock06.start from rfl,JFp_SHABlock06.checked]
  rw [show JFp_SHABlock06.result=JFp_SHABlock07.start from rfl,JFp_SHABlock07.checked]
  rw [show JFp_SHABlock07.result=JFp_SHABlock08.start from rfl,JFp_SHABlock08.checked]
  rw [show JFp_SHABlock08.result=JFp_SHABlock09.start from rfl,JFp_SHABlock09.checked]
  rw [show JFp_SHABlock09.result=JFp_SHABlock10.start from rfl,JFp_SHABlock10.checked]
  rw [show JFp_SHABlock10.result=JFp_SHABlock11.start from rfl,JFp_SHABlock11.checked]
  rw [show JFp_SHABlock11.result=JFp_SHABlock12.start from rfl,JFp_SHABlock12.checked]
  rw [show JFp_SHABlock12.result=JFp_SHABlock13.start from rfl,JFp_SHABlock13.checked]
  rw [show JFp_SHABlock13.result=JFp_SHABlock14.start from rfl,JFp_SHABlock14.checked]
  rw [show JFp_SHABlock14.result=JFp_SHABlock15.start from rfl,JFp_SHABlock15.checked]
  rw [show JFp_SHABlock15.result=JFp_SHABlock16.start from rfl,JFp_SHABlock16.checked]
  rw [show JFp_SHABlock16.result=JFp_SHABlock17.start from rfl,JFp_SHABlock17.checked]
  rw [show JFp_SHABlock17.result=JFp_SHABlock18.start from rfl,JFp_SHABlock18.checked]
  rw [show JFp_SHABlock18.result=JFp_SHABlock19.start from rfl,JFp_SHABlock19.checked]
  rw [show JFp_SHABlock19.result=JFp_SHABlock20.start from rfl,JFp_SHABlock20.checked]
  rw [show JFp_SHABlock20.result=JFp_SHABlock21.start from rfl,JFp_SHABlock21.checked]
  rw [show JFp_SHABlock21.result=JFp_SHABlock22.start from rfl,JFp_SHABlock22.checked]
  rw [show JFp_SHABlock22.result=JFp_SHABlock23.start from rfl,JFp_SHABlock23.checked]
  rw [show JFp_SHABlock23.result=JFp_SHABlock24.start from rfl,JFp_SHABlock24.checked]
#print axioms checked
end AspisR1.JFp_SeedHash
