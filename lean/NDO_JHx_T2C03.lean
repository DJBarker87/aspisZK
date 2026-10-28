import NDO_JHx_Blocks18
import NDO_JHx_Blocks19
import NDO_JHx_Blocks20
import NDO_JHe_SHAEquations2
import NDO_JGz_HashTools
set_option autoImplicit false
namespace AspisR1.JHx_T2C03
open JFp_SHA256
namespace H096
open JHe_C_Gr_M2.Hash096
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks18.B054.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks18.B055.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash096.tail).map Fin.val=JHe_C_Gr_M2.Hash096.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash096.message).map Fin.val=JHe_C_Gr_M2.Hash096.message := by
  simp only [JHe_C_Gr_M2.Hash096.message,JHe_C_Gr_M2.Hash096.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash096.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash096.message=JHe_C_Gr_M2.Hash096.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash096.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash096.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash096.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash096.message,JHe_C_Gr_M2.Hash096.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash096.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash096.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash096.message=JHe_C_Gr_M2.Hash096.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash096.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨96,by omega⟩)=JHe_SHAInputs2.expected ⟨96,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash096.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H096
namespace H097
open JHe_C_Gr_M2.Hash097
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks19.B000.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks19.B001.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash097.tail).map Fin.val=JHe_C_Gr_M2.Hash097.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash097.message).map Fin.val=JHe_C_Gr_M2.Hash097.message := by
  simp only [JHe_C_Gr_M2.Hash097.message,JHe_C_Gr_M2.Hash097.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash097.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash097.message=JHe_C_Gr_M2.Hash097.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash097.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash097.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash097.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash097.message,JHe_C_Gr_M2.Hash097.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash097.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash097.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash097.message=JHe_C_Gr_M2.Hash097.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash097.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨97,by omega⟩)=JHe_SHAInputs2.expected ⟨97,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash097.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H097
namespace H098
open JHe_C_Gr_M2.Hash098
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks19.B002.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks19.B003.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash098.tail).map Fin.val=JHe_C_Gr_M2.Hash098.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash098.message).map Fin.val=JHe_C_Gr_M2.Hash098.message := by
  simp only [JHe_C_Gr_M2.Hash098.message,JHe_C_Gr_M2.Hash098.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash098.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash098.message=JHe_C_Gr_M2.Hash098.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash098.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash098.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash098.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash098.message,JHe_C_Gr_M2.Hash098.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash098.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash098.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash098.message=JHe_C_Gr_M2.Hash098.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash098.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨98,by omega⟩)=JHe_SHAInputs2.expected ⟨98,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash098.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H098
namespace H099
open JHe_C_Gr_M2.Hash099
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks19.B004.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks19.B005.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash099.tail).map Fin.val=JHe_C_Gr_M2.Hash099.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash099.message).map Fin.val=JHe_C_Gr_M2.Hash099.message := by
  simp only [JHe_C_Gr_M2.Hash099.message,JHe_C_Gr_M2.Hash099.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash099.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash099.message=JHe_C_Gr_M2.Hash099.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash099.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash099.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash099.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash099.message,JHe_C_Gr_M2.Hash099.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash099.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash099.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash099.message=JHe_C_Gr_M2.Hash099.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash099.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨99,by omega⟩)=JHe_SHAInputs2.expected ⟨99,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash099.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H099
namespace H100
open JHe_C_Gr_M2.Hash100
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks19.B006.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks19.B007.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash100.tail).map Fin.val=JHe_C_Gr_M2.Hash100.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash100.message).map Fin.val=JHe_C_Gr_M2.Hash100.message := by
  simp only [JHe_C_Gr_M2.Hash100.message,JHe_C_Gr_M2.Hash100.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash100.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash100.message=JHe_C_Gr_M2.Hash100.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash100.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash100.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash100.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash100.message,JHe_C_Gr_M2.Hash100.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash100.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash100.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash100.message=JHe_C_Gr_M2.Hash100.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash100.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨100,by omega⟩)=JHe_SHAInputs2.expected ⟨100,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash100.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H100
namespace H101
open JHe_C_Gr_M2.Hash101
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks19.B008.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks19.B009.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash101.tail).map Fin.val=JHe_C_Gr_M2.Hash101.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash101.message).map Fin.val=JHe_C_Gr_M2.Hash101.message := by
  simp only [JHe_C_Gr_M2.Hash101.message,JHe_C_Gr_M2.Hash101.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash101.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash101.message=JHe_C_Gr_M2.Hash101.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash101.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash101.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash101.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash101.message,JHe_C_Gr_M2.Hash101.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash101.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash101.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash101.message=JHe_C_Gr_M2.Hash101.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash101.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨101,by omega⟩)=JHe_SHAInputs2.expected ⟨101,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash101.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H101
namespace H102
open JGc_TX2_M2.Hash126
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks19.B010.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks19.B011.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash126.tail).map Fin.val=JGc_TX2_M2.Hash126.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash126.message).map Fin.val=JGc_TX2_M2.Hash126.message := by
  simp only [JGc_TX2_M2.Hash126.message,JGc_TX2_M2.Hash126.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JGc_TX2_M2.Hash126.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JGc_TX2_M2.Hash126.message=JGc_TX2_M2.Hash126.chunks.flatten := by
  have size : JGc_TX2_M2.Hash126.message.length=65 := by
    simp only [JGc_TX2_M2.Hash126.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JGc_TX2_M2.Hash126.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JGc_TX2_M2.Hash126.message,JGc_TX2_M2.Hash126.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JGc_TX2_M2.Hash126.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JGc_TX2_M2.Hash126.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JGc_TX2_M2.Hash126.message=JGc_TX2_M2.Hash126.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JGc_TX2_M2.Hash126.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨102,by omega⟩)=JHe_SHAInputs2.expected ⟨102,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash126.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H102
namespace H103
open JHe_C_Gr_M2.Hash103
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks19.B012.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks19.B013.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash103.tail).map Fin.val=JHe_C_Gr_M2.Hash103.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash103.message).map Fin.val=JHe_C_Gr_M2.Hash103.message := by
  simp only [JHe_C_Gr_M2.Hash103.message,JHe_C_Gr_M2.Hash103.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash103.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash103.message=JHe_C_Gr_M2.Hash103.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash103.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash103.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash103.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash103.message,JHe_C_Gr_M2.Hash103.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash103.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash103.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash103.message=JHe_C_Gr_M2.Hash103.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash103.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨103,by omega⟩)=JHe_SHAInputs2.expected ⟨103,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash103.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H103
namespace H104
open JHe_C_Gr_M2.Hash104
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks19.B014.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks19.B015.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash104.tail).map Fin.val=JHe_C_Gr_M2.Hash104.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash104.message).map Fin.val=JHe_C_Gr_M2.Hash104.message := by
  simp only [JHe_C_Gr_M2.Hash104.message,JHe_C_Gr_M2.Hash104.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash104.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash104.message=JHe_C_Gr_M2.Hash104.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash104.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash104.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash104.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash104.message,JHe_C_Gr_M2.Hash104.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash104.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash104.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash104.message=JHe_C_Gr_M2.Hash104.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash104.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨104,by omega⟩)=JHe_SHAInputs2.expected ⟨104,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash104.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H104
namespace H105
open JHe_C_Gr_M2.Hash105
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks19.B016.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks19.B017.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash105.tail).map Fin.val=JHe_C_Gr_M2.Hash105.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash105.message).map Fin.val=JHe_C_Gr_M2.Hash105.message := by
  simp only [JHe_C_Gr_M2.Hash105.message,JHe_C_Gr_M2.Hash105.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash105.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash105.message=JHe_C_Gr_M2.Hash105.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash105.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash105.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash105.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash105.message,JHe_C_Gr_M2.Hash105.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash105.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash105.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash105.message=JHe_C_Gr_M2.Hash105.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash105.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨105,by omega⟩)=JHe_SHAInputs2.expected ⟨105,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash105.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H105
namespace H106
open JHe_C_Gr_M2.Hash106
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks19.B018.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks19.B019.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash106.tail).map Fin.val=JHe_C_Gr_M2.Hash106.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash106.message).map Fin.val=JHe_C_Gr_M2.Hash106.message := by
  simp only [JHe_C_Gr_M2.Hash106.message,JHe_C_Gr_M2.Hash106.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash106.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash106.message=JHe_C_Gr_M2.Hash106.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash106.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash106.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash106.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash106.message,JHe_C_Gr_M2.Hash106.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash106.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash106.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash106.message=JHe_C_Gr_M2.Hash106.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash106.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨106,by omega⟩)=JHe_SHAInputs2.expected ⟨106,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash106.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H106
namespace H107
open JHe_C_Gr_M2.Hash107
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks19.B020.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks19.B021.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash107.tail).map Fin.val=JHe_C_Gr_M2.Hash107.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash107.message).map Fin.val=JHe_C_Gr_M2.Hash107.message := by
  simp only [JHe_C_Gr_M2.Hash107.message,JHe_C_Gr_M2.Hash107.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash107.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash107.message=JHe_C_Gr_M2.Hash107.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash107.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash107.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash107.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash107.message,JHe_C_Gr_M2.Hash107.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash107.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash107.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash107.message=JHe_C_Gr_M2.Hash107.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash107.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨107,by omega⟩)=JHe_SHAInputs2.expected ⟨107,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash107.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H107
namespace H108
open JHe_C_Gr_M2.Hash108
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks19.B022.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks19.B023.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash108.tail).map Fin.val=JHe_C_Gr_M2.Hash108.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash108.message).map Fin.val=JHe_C_Gr_M2.Hash108.message := by
  simp only [JHe_C_Gr_M2.Hash108.message,JHe_C_Gr_M2.Hash108.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash108.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash108.message=JHe_C_Gr_M2.Hash108.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash108.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash108.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash108.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash108.message,JHe_C_Gr_M2.Hash108.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash108.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash108.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash108.message=JHe_C_Gr_M2.Hash108.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash108.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨108,by omega⟩)=JHe_SHAInputs2.expected ⟨108,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash108.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H108
namespace H109
open JHe_C_Gr_M2.Hash109
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks19.B024.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks19.B025.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash109.tail).map Fin.val=JHe_C_Gr_M2.Hash109.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash109.message).map Fin.val=JHe_C_Gr_M2.Hash109.message := by
  simp only [JHe_C_Gr_M2.Hash109.message,JHe_C_Gr_M2.Hash109.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash109.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash109.message=JHe_C_Gr_M2.Hash109.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash109.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash109.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash109.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash109.message,JHe_C_Gr_M2.Hash109.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash109.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash109.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash109.message=JHe_C_Gr_M2.Hash109.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash109.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨109,by omega⟩)=JHe_SHAInputs2.expected ⟨109,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash109.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H109
namespace H110
open JHe_C_Gr_M2.Hash110
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks19.B026.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks19.B027.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash110.tail).map Fin.val=JHe_C_Gr_M2.Hash110.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash110.message).map Fin.val=JHe_C_Gr_M2.Hash110.message := by
  simp only [JHe_C_Gr_M2.Hash110.message,JHe_C_Gr_M2.Hash110.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash110.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash110.message=JHe_C_Gr_M2.Hash110.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash110.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash110.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash110.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash110.message,JHe_C_Gr_M2.Hash110.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash110.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash110.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash110.message=JHe_C_Gr_M2.Hash110.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash110.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨110,by omega⟩)=JHe_SHAInputs2.expected ⟨110,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash110.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H110
namespace H111
open JHe_C_Gr_M2.Hash111
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks19.B028.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks19.B029.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash111.tail).map Fin.val=JHe_C_Gr_M2.Hash111.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash111.message).map Fin.val=JHe_C_Gr_M2.Hash111.message := by
  simp only [JHe_C_Gr_M2.Hash111.message,JHe_C_Gr_M2.Hash111.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash111.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash111.message=JHe_C_Gr_M2.Hash111.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash111.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash111.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash111.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash111.message,JHe_C_Gr_M2.Hash111.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash111.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash111.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash111.message=JHe_C_Gr_M2.Hash111.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash111.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨111,by omega⟩)=JHe_SHAInputs2.expected ⟨111,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash111.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H111
namespace H112
open JGc_TX2_M2.Hash137
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks19.B030.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks19.B031.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash137.tail).map Fin.val=JGc_TX2_M2.Hash137.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash137.message).map Fin.val=JGc_TX2_M2.Hash137.message := by
  simp only [JGc_TX2_M2.Hash137.message,JGc_TX2_M2.Hash137.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JGc_TX2_M2.Hash137.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JGc_TX2_M2.Hash137.message=JGc_TX2_M2.Hash137.chunks.flatten := by
  have size : JGc_TX2_M2.Hash137.message.length=65 := by
    simp only [JGc_TX2_M2.Hash137.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JGc_TX2_M2.Hash137.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JGc_TX2_M2.Hash137.message,JGc_TX2_M2.Hash137.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JGc_TX2_M2.Hash137.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JGc_TX2_M2.Hash137.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JGc_TX2_M2.Hash137.message=JGc_TX2_M2.Hash137.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JGc_TX2_M2.Hash137.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨112,by omega⟩)=JHe_SHAInputs2.expected ⟨112,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash137.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H112
namespace H113
open JHe_C_Gr_M2.Hash113
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks19.B032.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks19.B033.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash113.tail).map Fin.val=JHe_C_Gr_M2.Hash113.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash113.message).map Fin.val=JHe_C_Gr_M2.Hash113.message := by
  simp only [JHe_C_Gr_M2.Hash113.message,JHe_C_Gr_M2.Hash113.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash113.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash113.message=JHe_C_Gr_M2.Hash113.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash113.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash113.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash113.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash113.message,JHe_C_Gr_M2.Hash113.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash113.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash113.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash113.message=JHe_C_Gr_M2.Hash113.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash113.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨113,by omega⟩)=JHe_SHAInputs2.expected ⟨113,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash113.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H113
namespace H114
open JGc_TX2_M2.Hash140
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks19.B034.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks19.B035.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash140.tail).map Fin.val=JGc_TX2_M2.Hash140.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash140.message).map Fin.val=JGc_TX2_M2.Hash140.message := by
  simp only [JGc_TX2_M2.Hash140.message,JGc_TX2_M2.Hash140.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JGc_TX2_M2.Hash140.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JGc_TX2_M2.Hash140.message=JGc_TX2_M2.Hash140.chunks.flatten := by
  have size : JGc_TX2_M2.Hash140.message.length=65 := by
    simp only [JGc_TX2_M2.Hash140.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JGc_TX2_M2.Hash140.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JGc_TX2_M2.Hash140.message,JGc_TX2_M2.Hash140.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JGc_TX2_M2.Hash140.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JGc_TX2_M2.Hash140.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JGc_TX2_M2.Hash140.message=JGc_TX2_M2.Hash140.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JGc_TX2_M2.Hash140.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨114,by omega⟩)=JHe_SHAInputs2.expected ⟨114,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash140.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H114
namespace H115
open JHe_C_Gr_M2.Hash115
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks19.B036.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks19.B037.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash115.tail).map Fin.val=JHe_C_Gr_M2.Hash115.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash115.message).map Fin.val=JHe_C_Gr_M2.Hash115.message := by
  simp only [JHe_C_Gr_M2.Hash115.message,JHe_C_Gr_M2.Hash115.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash115.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash115.message=JHe_C_Gr_M2.Hash115.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash115.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash115.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash115.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash115.message,JHe_C_Gr_M2.Hash115.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash115.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash115.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash115.message=JHe_C_Gr_M2.Hash115.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash115.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨115,by omega⟩)=JHe_SHAInputs2.expected ⟨115,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash115.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H115
namespace H116
open JHe_C_Gr_M2.Hash116
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks19.B038.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks19.B039.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash116.tail).map Fin.val=JHe_C_Gr_M2.Hash116.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash116.message).map Fin.val=JHe_C_Gr_M2.Hash116.message := by
  simp only [JHe_C_Gr_M2.Hash116.message,JHe_C_Gr_M2.Hash116.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash116.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash116.message=JHe_C_Gr_M2.Hash116.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash116.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash116.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash116.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash116.message,JHe_C_Gr_M2.Hash116.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash116.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash116.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash116.message=JHe_C_Gr_M2.Hash116.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash116.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨116,by omega⟩)=JHe_SHAInputs2.expected ⟨116,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash116.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H116
namespace H117
open JGc_TX2_M2.Hash141
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks19.B040.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks19.B041.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash141.tail).map Fin.val=JGc_TX2_M2.Hash141.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash141.message).map Fin.val=JGc_TX2_M2.Hash141.message := by
  simp only [JGc_TX2_M2.Hash141.message,JGc_TX2_M2.Hash141.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JGc_TX2_M2.Hash141.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JGc_TX2_M2.Hash141.message=JGc_TX2_M2.Hash141.chunks.flatten := by
  have size : JGc_TX2_M2.Hash141.message.length=65 := by
    simp only [JGc_TX2_M2.Hash141.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JGc_TX2_M2.Hash141.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JGc_TX2_M2.Hash141.message,JGc_TX2_M2.Hash141.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JGc_TX2_M2.Hash141.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JGc_TX2_M2.Hash141.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JGc_TX2_M2.Hash141.message=JGc_TX2_M2.Hash141.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JGc_TX2_M2.Hash141.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨117,by omega⟩)=JHe_SHAInputs2.expected ⟨117,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash141.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H117
namespace H118
open JHe_C_Gr_M2.Hash118
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks19.B042.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks19.B043.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash118.tail).map Fin.val=JHe_C_Gr_M2.Hash118.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash118.message).map Fin.val=JHe_C_Gr_M2.Hash118.message := by
  simp only [JHe_C_Gr_M2.Hash118.message,JHe_C_Gr_M2.Hash118.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash118.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash118.message=JHe_C_Gr_M2.Hash118.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash118.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash118.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash118.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash118.message,JHe_C_Gr_M2.Hash118.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash118.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash118.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash118.message=JHe_C_Gr_M2.Hash118.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash118.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨118,by omega⟩)=JHe_SHAInputs2.expected ⟨118,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash118.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H118
namespace H119
open JHe_C_Gr_M2.Hash119
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks19.B044.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks19.B045.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash119.tail).map Fin.val=JHe_C_Gr_M2.Hash119.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash119.message).map Fin.val=JHe_C_Gr_M2.Hash119.message := by
  simp only [JHe_C_Gr_M2.Hash119.message,JHe_C_Gr_M2.Hash119.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash119.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash119.message=JHe_C_Gr_M2.Hash119.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash119.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash119.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash119.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash119.message,JHe_C_Gr_M2.Hash119.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash119.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash119.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash119.message=JHe_C_Gr_M2.Hash119.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash119.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨119,by omega⟩)=JHe_SHAInputs2.expected ⟨119,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash119.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H119
namespace H120
open JHe_C_Gr_M2.Hash120
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks19.B046.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks19.B047.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash120.tail).map Fin.val=JHe_C_Gr_M2.Hash120.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash120.message).map Fin.val=JHe_C_Gr_M2.Hash120.message := by
  simp only [JHe_C_Gr_M2.Hash120.message,JHe_C_Gr_M2.Hash120.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash120.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash120.message=JHe_C_Gr_M2.Hash120.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash120.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash120.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash120.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash120.message,JHe_C_Gr_M2.Hash120.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash120.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash120.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash120.message=JHe_C_Gr_M2.Hash120.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash120.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨120,by omega⟩)=JHe_SHAInputs2.expected ⟨120,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash120.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H120
namespace H121
open JGc_TX2_M2.Hash147
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks19.B048.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks19.B049.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash147.tail).map Fin.val=JGc_TX2_M2.Hash147.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash147.message).map Fin.val=JGc_TX2_M2.Hash147.message := by
  simp only [JGc_TX2_M2.Hash147.message,JGc_TX2_M2.Hash147.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JGc_TX2_M2.Hash147.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JGc_TX2_M2.Hash147.message=JGc_TX2_M2.Hash147.chunks.flatten := by
  have size : JGc_TX2_M2.Hash147.message.length=65 := by
    simp only [JGc_TX2_M2.Hash147.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JGc_TX2_M2.Hash147.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JGc_TX2_M2.Hash147.message,JGc_TX2_M2.Hash147.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JGc_TX2_M2.Hash147.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JGc_TX2_M2.Hash147.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JGc_TX2_M2.Hash147.message=JGc_TX2_M2.Hash147.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JGc_TX2_M2.Hash147.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨121,by omega⟩)=JHe_SHAInputs2.expected ⟨121,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash147.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H121
namespace H122
open JGc_TX2_M2.Hash149
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks19.B050.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks19.B051.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash149.tail).map Fin.val=JGc_TX2_M2.Hash149.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash149.message).map Fin.val=JGc_TX2_M2.Hash149.message := by
  simp only [JGc_TX2_M2.Hash149.message,JGc_TX2_M2.Hash149.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JGc_TX2_M2.Hash149.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JGc_TX2_M2.Hash149.message=JGc_TX2_M2.Hash149.chunks.flatten := by
  have size : JGc_TX2_M2.Hash149.message.length=65 := by
    simp only [JGc_TX2_M2.Hash149.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JGc_TX2_M2.Hash149.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JGc_TX2_M2.Hash149.message,JGc_TX2_M2.Hash149.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JGc_TX2_M2.Hash149.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JGc_TX2_M2.Hash149.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JGc_TX2_M2.Hash149.message=JGc_TX2_M2.Hash149.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JGc_TX2_M2.Hash149.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨122,by omega⟩)=JHe_SHAInputs2.expected ⟨122,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash149.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H122
namespace H123
open JHe_C_Gr_M2.Hash123
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks19.B052.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks19.B053.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash123.tail).map Fin.val=JHe_C_Gr_M2.Hash123.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash123.message).map Fin.val=JHe_C_Gr_M2.Hash123.message := by
  simp only [JHe_C_Gr_M2.Hash123.message,JHe_C_Gr_M2.Hash123.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash123.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash123.message=JHe_C_Gr_M2.Hash123.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash123.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash123.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash123.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash123.message,JHe_C_Gr_M2.Hash123.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash123.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash123.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash123.message=JHe_C_Gr_M2.Hash123.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash123.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨123,by omega⟩)=JHe_SHAInputs2.expected ⟨123,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash123.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H123
namespace H124
open JGc_TX2_M2.Hash150
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks19.B054.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks19.B055.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash150.tail).map Fin.val=JGc_TX2_M2.Hash150.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash150.message).map Fin.val=JGc_TX2_M2.Hash150.message := by
  simp only [JGc_TX2_M2.Hash150.message,JGc_TX2_M2.Hash150.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JGc_TX2_M2.Hash150.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JGc_TX2_M2.Hash150.message=JGc_TX2_M2.Hash150.chunks.flatten := by
  have size : JGc_TX2_M2.Hash150.message.length=65 := by
    simp only [JGc_TX2_M2.Hash150.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JGc_TX2_M2.Hash150.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JGc_TX2_M2.Hash150.message,JGc_TX2_M2.Hash150.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JGc_TX2_M2.Hash150.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JGc_TX2_M2.Hash150.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JGc_TX2_M2.Hash150.message=JGc_TX2_M2.Hash150.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JGc_TX2_M2.Hash150.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨124,by omega⟩)=JHe_SHAInputs2.expected ⟨124,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash150.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H124
namespace H125
open JHe_C_Gr_M2.Hash125
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks20.B000.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks20.B001.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash125.tail).map Fin.val=JHe_C_Gr_M2.Hash125.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash125.message).map Fin.val=JHe_C_Gr_M2.Hash125.message := by
  simp only [JHe_C_Gr_M2.Hash125.message,JHe_C_Gr_M2.Hash125.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash125.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash125.message=JHe_C_Gr_M2.Hash125.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash125.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash125.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash125.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash125.message,JHe_C_Gr_M2.Hash125.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash125.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash125.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash125.message=JHe_C_Gr_M2.Hash125.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash125.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨125,by omega⟩)=JHe_SHAInputs2.expected ⟨125,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash125.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H125
namespace H126
open JHe_C_Gr_M2.Hash126
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks20.B002.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks20.B003.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash126.tail).map Fin.val=JHe_C_Gr_M2.Hash126.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash126.message).map Fin.val=JHe_C_Gr_M2.Hash126.message := by
  simp only [JHe_C_Gr_M2.Hash126.message,JHe_C_Gr_M2.Hash126.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash126.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash126.message=JHe_C_Gr_M2.Hash126.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash126.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash126.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash126.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash126.message,JHe_C_Gr_M2.Hash126.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash126.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash126.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash126.message=JHe_C_Gr_M2.Hash126.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash126.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨126,by omega⟩)=JHe_SHAInputs2.expected ⟨126,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash126.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H126
namespace H127
open JGc_TX2_M2.Hash153
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks20.B004.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks20.B005.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash153.tail).map Fin.val=JGc_TX2_M2.Hash153.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash153.message).map Fin.val=JGc_TX2_M2.Hash153.message := by
  simp only [JGc_TX2_M2.Hash153.message,JGc_TX2_M2.Hash153.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JGc_TX2_M2.Hash153.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JGc_TX2_M2.Hash153.message=JGc_TX2_M2.Hash153.chunks.flatten := by
  have size : JGc_TX2_M2.Hash153.message.length=65 := by
    simp only [JGc_TX2_M2.Hash153.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JGc_TX2_M2.Hash153.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JGc_TX2_M2.Hash153.message,JGc_TX2_M2.Hash153.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JGc_TX2_M2.Hash153.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JGc_TX2_M2.Hash153.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JGc_TX2_M2.Hash153.message=JGc_TX2_M2.Hash153.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JGc_TX2_M2.Hash153.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨127,by omega⟩)=JHe_SHAInputs2.expected ⟨127,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash153.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H127
end AspisR1.JHx_T2C03
