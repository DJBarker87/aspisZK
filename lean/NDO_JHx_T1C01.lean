import NDO_JHx_Blocks10
import NDO_JHx_Blocks11
import NDO_JHx_Blocks12
import NDO_JHe_SHAEquations1
import NDO_JGz_HashTools
set_option autoImplicit false
namespace AspisR1.JHx_T1C01
open JFp_SHA256
namespace H032
open JHe_C_Gr_M1.Hash032
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks10.B050.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks10.B051.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash032.tail).map Fin.val=JHe_C_Gr_M1.Hash032.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash032.message).map Fin.val=JHe_C_Gr_M1.Hash032.message := by
  simp only [JHe_C_Gr_M1.Hash032.message,JHe_C_Gr_M1.Hash032.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash032.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash032.message=JHe_C_Gr_M1.Hash032.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash032.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash032.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash032.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash032.message,JHe_C_Gr_M1.Hash032.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash032.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash032.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash032.message=JHe_C_Gr_M1.Hash032.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash032.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨32,by omega⟩)=JHe_SHAInputs1.expected ⟨32,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash032.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H032
namespace H033
open JHe_C_Gr_M1.Hash033
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks10.B052.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks10.B053.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash033.tail).map Fin.val=JHe_C_Gr_M1.Hash033.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash033.message).map Fin.val=JHe_C_Gr_M1.Hash033.message := by
  simp only [JHe_C_Gr_M1.Hash033.message,JHe_C_Gr_M1.Hash033.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash033.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash033.message=JHe_C_Gr_M1.Hash033.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash033.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash033.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash033.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash033.message,JHe_C_Gr_M1.Hash033.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash033.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash033.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash033.message=JHe_C_Gr_M1.Hash033.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash033.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨33,by omega⟩)=JHe_SHAInputs1.expected ⟨33,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash033.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H033
namespace H034
open JHe_C_Gr_M1.Hash034
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks10.B054.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks10.B055.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash034.tail).map Fin.val=JHe_C_Gr_M1.Hash034.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash034.message).map Fin.val=JHe_C_Gr_M1.Hash034.message := by
  simp only [JHe_C_Gr_M1.Hash034.message,JHe_C_Gr_M1.Hash034.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash034.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash034.message=JHe_C_Gr_M1.Hash034.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash034.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash034.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash034.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash034.message,JHe_C_Gr_M1.Hash034.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash034.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash034.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash034.message=JHe_C_Gr_M1.Hash034.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash034.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨34,by omega⟩)=JHe_SHAInputs1.expected ⟨34,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash034.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H034
namespace H035
open JHe_C_Gr_M1.Hash035
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks11.B000.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks11.B001.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash035.tail).map Fin.val=JHe_C_Gr_M1.Hash035.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash035.message).map Fin.val=JHe_C_Gr_M1.Hash035.message := by
  simp only [JHe_C_Gr_M1.Hash035.message,JHe_C_Gr_M1.Hash035.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash035.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash035.message=JHe_C_Gr_M1.Hash035.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash035.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash035.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash035.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash035.message,JHe_C_Gr_M1.Hash035.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash035.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash035.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash035.message=JHe_C_Gr_M1.Hash035.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash035.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨35,by omega⟩)=JHe_SHAInputs1.expected ⟨35,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash035.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H035
namespace H036
open JHe_C_Gr_M1.Hash036
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks11.B002.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks11.B003.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash036.tail).map Fin.val=JHe_C_Gr_M1.Hash036.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash036.message).map Fin.val=JHe_C_Gr_M1.Hash036.message := by
  simp only [JHe_C_Gr_M1.Hash036.message,JHe_C_Gr_M1.Hash036.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash036.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash036.message=JHe_C_Gr_M1.Hash036.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash036.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash036.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash036.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash036.message,JHe_C_Gr_M1.Hash036.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash036.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash036.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash036.message=JHe_C_Gr_M1.Hash036.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash036.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨36,by omega⟩)=JHe_SHAInputs1.expected ⟨36,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash036.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H036
namespace H037
open JHe_C_Gr_M1.Hash037
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks11.B004.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks11.B005.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash037.tail).map Fin.val=JHe_C_Gr_M1.Hash037.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash037.message).map Fin.val=JHe_C_Gr_M1.Hash037.message := by
  simp only [JHe_C_Gr_M1.Hash037.message,JHe_C_Gr_M1.Hash037.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash037.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash037.message=JHe_C_Gr_M1.Hash037.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash037.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash037.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash037.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash037.message,JHe_C_Gr_M1.Hash037.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash037.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash037.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash037.message=JHe_C_Gr_M1.Hash037.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash037.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨37,by omega⟩)=JHe_SHAInputs1.expected ⟨37,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash037.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H037
namespace H038
open JHe_C_Gr_M1.Hash038
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks11.B006.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks11.B007.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash038.tail).map Fin.val=JHe_C_Gr_M1.Hash038.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash038.message).map Fin.val=JHe_C_Gr_M1.Hash038.message := by
  simp only [JHe_C_Gr_M1.Hash038.message,JHe_C_Gr_M1.Hash038.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash038.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash038.message=JHe_C_Gr_M1.Hash038.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash038.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash038.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash038.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash038.message,JHe_C_Gr_M1.Hash038.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash038.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash038.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash038.message=JHe_C_Gr_M1.Hash038.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash038.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨38,by omega⟩)=JHe_SHAInputs1.expected ⟨38,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash038.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H038
namespace H039
open JHe_C_Gr_M1.Hash039
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks11.B008.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks11.B009.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash039.tail).map Fin.val=JHe_C_Gr_M1.Hash039.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash039.message).map Fin.val=JHe_C_Gr_M1.Hash039.message := by
  simp only [JHe_C_Gr_M1.Hash039.message,JHe_C_Gr_M1.Hash039.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash039.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash039.message=JHe_C_Gr_M1.Hash039.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash039.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash039.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash039.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash039.message,JHe_C_Gr_M1.Hash039.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash039.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash039.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash039.message=JHe_C_Gr_M1.Hash039.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash039.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨39,by omega⟩)=JHe_SHAInputs1.expected ⟨39,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash039.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H039
namespace H040
open JHe_C_Gr_M1.Hash040
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks11.B010.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks11.B011.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash040.tail).map Fin.val=JHe_C_Gr_M1.Hash040.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash040.message).map Fin.val=JHe_C_Gr_M1.Hash040.message := by
  simp only [JHe_C_Gr_M1.Hash040.message,JHe_C_Gr_M1.Hash040.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash040.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash040.message=JHe_C_Gr_M1.Hash040.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash040.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash040.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash040.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash040.message,JHe_C_Gr_M1.Hash040.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash040.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash040.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash040.message=JHe_C_Gr_M1.Hash040.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash040.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨40,by omega⟩)=JHe_SHAInputs1.expected ⟨40,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash040.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H040
namespace H041
open JHe_C_Gr_M1.Hash041
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks11.B012.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks11.B013.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash041.tail).map Fin.val=JHe_C_Gr_M1.Hash041.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash041.message).map Fin.val=JHe_C_Gr_M1.Hash041.message := by
  simp only [JHe_C_Gr_M1.Hash041.message,JHe_C_Gr_M1.Hash041.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash041.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash041.message=JHe_C_Gr_M1.Hash041.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash041.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash041.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash041.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash041.message,JHe_C_Gr_M1.Hash041.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash041.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash041.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash041.message=JHe_C_Gr_M1.Hash041.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash041.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨41,by omega⟩)=JHe_SHAInputs1.expected ⟨41,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash041.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H041
namespace H042
open JHe_C_Gr_M1.Hash042
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks11.B014.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks11.B015.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash042.tail).map Fin.val=JHe_C_Gr_M1.Hash042.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash042.message).map Fin.val=JHe_C_Gr_M1.Hash042.message := by
  simp only [JHe_C_Gr_M1.Hash042.message,JHe_C_Gr_M1.Hash042.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash042.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash042.message=JHe_C_Gr_M1.Hash042.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash042.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash042.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash042.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash042.message,JHe_C_Gr_M1.Hash042.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash042.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash042.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash042.message=JHe_C_Gr_M1.Hash042.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash042.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨42,by omega⟩)=JHe_SHAInputs1.expected ⟨42,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash042.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H042
namespace H043
open JHe_C_Gr_M1.Hash043
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks11.B016.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks11.B017.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash043.tail).map Fin.val=JHe_C_Gr_M1.Hash043.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash043.message).map Fin.val=JHe_C_Gr_M1.Hash043.message := by
  simp only [JHe_C_Gr_M1.Hash043.message,JHe_C_Gr_M1.Hash043.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash043.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash043.message=JHe_C_Gr_M1.Hash043.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash043.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash043.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash043.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash043.message,JHe_C_Gr_M1.Hash043.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash043.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash043.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash043.message=JHe_C_Gr_M1.Hash043.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash043.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨43,by omega⟩)=JHe_SHAInputs1.expected ⟨43,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash043.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H043
namespace H044
open JHe_C_Gr_M1.Hash044
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks11.B018.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks11.B019.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash044.tail).map Fin.val=JHe_C_Gr_M1.Hash044.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash044.message).map Fin.val=JHe_C_Gr_M1.Hash044.message := by
  simp only [JHe_C_Gr_M1.Hash044.message,JHe_C_Gr_M1.Hash044.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash044.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash044.message=JHe_C_Gr_M1.Hash044.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash044.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash044.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash044.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash044.message,JHe_C_Gr_M1.Hash044.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash044.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash044.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash044.message=JHe_C_Gr_M1.Hash044.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash044.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨44,by omega⟩)=JHe_SHAInputs1.expected ⟨44,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash044.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H044
namespace H045
open JHe_C_Gr_M1.Hash045
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks11.B020.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks11.B021.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash045.tail).map Fin.val=JHe_C_Gr_M1.Hash045.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash045.message).map Fin.val=JHe_C_Gr_M1.Hash045.message := by
  simp only [JHe_C_Gr_M1.Hash045.message,JHe_C_Gr_M1.Hash045.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash045.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash045.message=JHe_C_Gr_M1.Hash045.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash045.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash045.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash045.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash045.message,JHe_C_Gr_M1.Hash045.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash045.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash045.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash045.message=JHe_C_Gr_M1.Hash045.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash045.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨45,by omega⟩)=JHe_SHAInputs1.expected ⟨45,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash045.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H045
namespace H046
open JHe_C_Gr_M1.Hash046
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks11.B022.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks11.B023.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash046.tail).map Fin.val=JHe_C_Gr_M1.Hash046.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash046.message).map Fin.val=JHe_C_Gr_M1.Hash046.message := by
  simp only [JHe_C_Gr_M1.Hash046.message,JHe_C_Gr_M1.Hash046.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash046.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash046.message=JHe_C_Gr_M1.Hash046.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash046.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash046.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash046.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash046.message,JHe_C_Gr_M1.Hash046.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash046.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash046.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash046.message=JHe_C_Gr_M1.Hash046.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash046.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨46,by omega⟩)=JHe_SHAInputs1.expected ⟨46,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash046.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H046
namespace H047
open JHe_C_Gr_M1.Hash047
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks11.B024.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks11.B025.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash047.tail).map Fin.val=JHe_C_Gr_M1.Hash047.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash047.message).map Fin.val=JHe_C_Gr_M1.Hash047.message := by
  simp only [JHe_C_Gr_M1.Hash047.message,JHe_C_Gr_M1.Hash047.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash047.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash047.message=JHe_C_Gr_M1.Hash047.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash047.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash047.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash047.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash047.message,JHe_C_Gr_M1.Hash047.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash047.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash047.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash047.message=JHe_C_Gr_M1.Hash047.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash047.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨47,by omega⟩)=JHe_SHAInputs1.expected ⟨47,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash047.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H047
namespace H048
open JHe_C_Gr_M1.Hash048
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks11.B026.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks11.B027.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash048.tail).map Fin.val=JHe_C_Gr_M1.Hash048.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash048.message).map Fin.val=JHe_C_Gr_M1.Hash048.message := by
  simp only [JHe_C_Gr_M1.Hash048.message,JHe_C_Gr_M1.Hash048.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash048.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash048.message=JHe_C_Gr_M1.Hash048.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash048.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash048.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash048.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash048.message,JHe_C_Gr_M1.Hash048.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash048.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash048.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash048.message=JHe_C_Gr_M1.Hash048.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash048.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨48,by omega⟩)=JHe_SHAInputs1.expected ⟨48,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash048.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H048
namespace H049
open JHe_C_Gr_M1.Hash049
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks11.B028.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks11.B029.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash049.tail).map Fin.val=JHe_C_Gr_M1.Hash049.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash049.message).map Fin.val=JHe_C_Gr_M1.Hash049.message := by
  simp only [JHe_C_Gr_M1.Hash049.message,JHe_C_Gr_M1.Hash049.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash049.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash049.message=JHe_C_Gr_M1.Hash049.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash049.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash049.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash049.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash049.message,JHe_C_Gr_M1.Hash049.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash049.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash049.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash049.message=JHe_C_Gr_M1.Hash049.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash049.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨49,by omega⟩)=JHe_SHAInputs1.expected ⟨49,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash049.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H049
namespace H050
open JHe_C_Gr_M1.Hash050
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks11.B030.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks11.B031.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash050.tail).map Fin.val=JHe_C_Gr_M1.Hash050.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash050.message).map Fin.val=JHe_C_Gr_M1.Hash050.message := by
  simp only [JHe_C_Gr_M1.Hash050.message,JHe_C_Gr_M1.Hash050.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash050.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash050.message=JHe_C_Gr_M1.Hash050.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash050.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash050.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash050.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash050.message,JHe_C_Gr_M1.Hash050.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash050.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash050.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash050.message=JHe_C_Gr_M1.Hash050.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash050.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨50,by omega⟩)=JHe_SHAInputs1.expected ⟨50,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash050.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H050
namespace H051
open JHe_C_Gr_M1.Hash051
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks11.B032.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks11.B033.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash051.tail).map Fin.val=JHe_C_Gr_M1.Hash051.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash051.message).map Fin.val=JHe_C_Gr_M1.Hash051.message := by
  simp only [JHe_C_Gr_M1.Hash051.message,JHe_C_Gr_M1.Hash051.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash051.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash051.message=JHe_C_Gr_M1.Hash051.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash051.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash051.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash051.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash051.message,JHe_C_Gr_M1.Hash051.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash051.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash051.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash051.message=JHe_C_Gr_M1.Hash051.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash051.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨51,by omega⟩)=JHe_SHAInputs1.expected ⟨51,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash051.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H051
namespace H052
open JHe_C_Gr_M1.Hash052
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks11.B034.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks11.B035.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash052.tail).map Fin.val=JHe_C_Gr_M1.Hash052.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash052.message).map Fin.val=JHe_C_Gr_M1.Hash052.message := by
  simp only [JHe_C_Gr_M1.Hash052.message,JHe_C_Gr_M1.Hash052.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash052.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash052.message=JHe_C_Gr_M1.Hash052.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash052.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash052.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash052.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash052.message,JHe_C_Gr_M1.Hash052.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash052.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash052.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash052.message=JHe_C_Gr_M1.Hash052.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash052.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨52,by omega⟩)=JHe_SHAInputs1.expected ⟨52,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash052.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H052
namespace H053
open JHe_C_Gr_M1.Hash053
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks11.B036.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks11.B037.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash053.tail).map Fin.val=JHe_C_Gr_M1.Hash053.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash053.message).map Fin.val=JHe_C_Gr_M1.Hash053.message := by
  simp only [JHe_C_Gr_M1.Hash053.message,JHe_C_Gr_M1.Hash053.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash053.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash053.message=JHe_C_Gr_M1.Hash053.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash053.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash053.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash053.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash053.message,JHe_C_Gr_M1.Hash053.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash053.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash053.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash053.message=JHe_C_Gr_M1.Hash053.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash053.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨53,by omega⟩)=JHe_SHAInputs1.expected ⟨53,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash053.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H053
namespace H054
open JHe_C_Gr_M1.Hash054
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks11.B038.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks11.B039.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash054.tail).map Fin.val=JHe_C_Gr_M1.Hash054.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash054.message).map Fin.val=JHe_C_Gr_M1.Hash054.message := by
  simp only [JHe_C_Gr_M1.Hash054.message,JHe_C_Gr_M1.Hash054.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash054.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash054.message=JHe_C_Gr_M1.Hash054.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash054.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash054.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash054.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash054.message,JHe_C_Gr_M1.Hash054.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash054.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash054.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash054.message=JHe_C_Gr_M1.Hash054.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash054.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨54,by omega⟩)=JHe_SHAInputs1.expected ⟨54,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash054.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H054
namespace H055
open JHe_C_Gr_M1.Hash055
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks11.B040.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks11.B041.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash055.tail).map Fin.val=JHe_C_Gr_M1.Hash055.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash055.message).map Fin.val=JHe_C_Gr_M1.Hash055.message := by
  simp only [JHe_C_Gr_M1.Hash055.message,JHe_C_Gr_M1.Hash055.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash055.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash055.message=JHe_C_Gr_M1.Hash055.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash055.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash055.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash055.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash055.message,JHe_C_Gr_M1.Hash055.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash055.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash055.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash055.message=JHe_C_Gr_M1.Hash055.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash055.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨55,by omega⟩)=JHe_SHAInputs1.expected ⟨55,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash055.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H055
namespace H056
open JHe_C_Gr_M1.Hash056
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks11.B042.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks11.B043.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash056.tail).map Fin.val=JHe_C_Gr_M1.Hash056.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash056.message).map Fin.val=JHe_C_Gr_M1.Hash056.message := by
  simp only [JHe_C_Gr_M1.Hash056.message,JHe_C_Gr_M1.Hash056.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash056.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash056.message=JHe_C_Gr_M1.Hash056.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash056.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash056.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash056.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash056.message,JHe_C_Gr_M1.Hash056.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash056.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash056.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash056.message=JHe_C_Gr_M1.Hash056.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash056.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨56,by omega⟩)=JHe_SHAInputs1.expected ⟨56,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash056.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H056
namespace H057
open JHe_C_Gr_M1.Hash057
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks11.B044.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks11.B045.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash057.tail).map Fin.val=JHe_C_Gr_M1.Hash057.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash057.message).map Fin.val=JHe_C_Gr_M1.Hash057.message := by
  simp only [JHe_C_Gr_M1.Hash057.message,JHe_C_Gr_M1.Hash057.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash057.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash057.message=JHe_C_Gr_M1.Hash057.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash057.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash057.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash057.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash057.message,JHe_C_Gr_M1.Hash057.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash057.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash057.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash057.message=JHe_C_Gr_M1.Hash057.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash057.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨57,by omega⟩)=JHe_SHAInputs1.expected ⟨57,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash057.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H057
namespace H058
open JHe_C_Gr_M1.Hash058
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks11.B046.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks11.B047.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash058.tail).map Fin.val=JHe_C_Gr_M1.Hash058.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash058.message).map Fin.val=JHe_C_Gr_M1.Hash058.message := by
  simp only [JHe_C_Gr_M1.Hash058.message,JHe_C_Gr_M1.Hash058.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash058.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash058.message=JHe_C_Gr_M1.Hash058.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash058.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash058.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash058.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash058.message,JHe_C_Gr_M1.Hash058.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash058.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash058.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash058.message=JHe_C_Gr_M1.Hash058.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash058.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨58,by omega⟩)=JHe_SHAInputs1.expected ⟨58,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash058.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H058
namespace H059
open JHe_C_Gr_M1.Hash059
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks11.B048.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks11.B049.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash059.tail).map Fin.val=JHe_C_Gr_M1.Hash059.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash059.message).map Fin.val=JHe_C_Gr_M1.Hash059.message := by
  simp only [JHe_C_Gr_M1.Hash059.message,JHe_C_Gr_M1.Hash059.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash059.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash059.message=JHe_C_Gr_M1.Hash059.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash059.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash059.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash059.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash059.message,JHe_C_Gr_M1.Hash059.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash059.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash059.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash059.message=JHe_C_Gr_M1.Hash059.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash059.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨59,by omega⟩)=JHe_SHAInputs1.expected ⟨59,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash059.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H059
namespace H060
open JHe_C_Gr_M1.Hash060
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks11.B050.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks11.B051.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash060.tail).map Fin.val=JHe_C_Gr_M1.Hash060.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash060.message).map Fin.val=JHe_C_Gr_M1.Hash060.message := by
  simp only [JHe_C_Gr_M1.Hash060.message,JHe_C_Gr_M1.Hash060.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash060.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash060.message=JHe_C_Gr_M1.Hash060.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash060.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash060.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash060.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash060.message,JHe_C_Gr_M1.Hash060.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash060.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash060.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash060.message=JHe_C_Gr_M1.Hash060.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash060.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨60,by omega⟩)=JHe_SHAInputs1.expected ⟨60,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash060.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H060
namespace H061
open JHe_C_Gr_M1.Hash061
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks11.B052.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks11.B053.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash061.tail).map Fin.val=JHe_C_Gr_M1.Hash061.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash061.message).map Fin.val=JHe_C_Gr_M1.Hash061.message := by
  simp only [JHe_C_Gr_M1.Hash061.message,JHe_C_Gr_M1.Hash061.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash061.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash061.message=JHe_C_Gr_M1.Hash061.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash061.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash061.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash061.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash061.message,JHe_C_Gr_M1.Hash061.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash061.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash061.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash061.message=JHe_C_Gr_M1.Hash061.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash061.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨61,by omega⟩)=JHe_SHAInputs1.expected ⟨61,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash061.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H061
namespace H062
open JHe_C_Gr_M1.Hash062
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks11.B054.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks11.B055.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash062.tail).map Fin.val=JHe_C_Gr_M1.Hash062.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash062.message).map Fin.val=JHe_C_Gr_M1.Hash062.message := by
  simp only [JHe_C_Gr_M1.Hash062.message,JHe_C_Gr_M1.Hash062.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash062.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash062.message=JHe_C_Gr_M1.Hash062.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash062.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash062.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash062.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash062.message,JHe_C_Gr_M1.Hash062.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash062.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash062.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash062.message=JHe_C_Gr_M1.Hash062.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash062.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨62,by omega⟩)=JHe_SHAInputs1.expected ⟨62,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash062.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H062
namespace H063
open JHe_C_Gr_M1.Hash063
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks12.B000.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks12.B001.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash063.tail).map Fin.val=JHe_C_Gr_M1.Hash063.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash063.message).map Fin.val=JHe_C_Gr_M1.Hash063.message := by
  simp only [JHe_C_Gr_M1.Hash063.message,JHe_C_Gr_M1.Hash063.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash063.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash063.message=JHe_C_Gr_M1.Hash063.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash063.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash063.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash063.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash063.message,JHe_C_Gr_M1.Hash063.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash063.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash063.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash063.message=JHe_C_Gr_M1.Hash063.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash063.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨63,by omega⟩)=JHe_SHAInputs1.expected ⟨63,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash063.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H063
end AspisR1.JHx_T1C01
