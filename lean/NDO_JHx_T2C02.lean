import NDO_JHx_Blocks17
import NDO_JHx_Blocks18
import NDO_JHe_SHAEquations2
import NDO_JGz_HashTools
set_option autoImplicit false
namespace AspisR1.JHx_T2C02
open JFp_SHA256
namespace H064
open JHe_C_Gr_M2.Hash064
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks17.B046.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks17.B047.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash064.tail).map Fin.val=JHe_C_Gr_M2.Hash064.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash064.message).map Fin.val=JHe_C_Gr_M2.Hash064.message := by
  simp only [JHe_C_Gr_M2.Hash064.message,JHe_C_Gr_M2.Hash064.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash064.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash064.message=JHe_C_Gr_M2.Hash064.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash064.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash064.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash064.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash064.message,JHe_C_Gr_M2.Hash064.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash064.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash064.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash064.message=JHe_C_Gr_M2.Hash064.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash064.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨64,by omega⟩)=JHe_SHAInputs2.expected ⟨64,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash064.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H064
namespace H065
open JHe_C_Gr_M2.Hash065
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks17.B048.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks17.B049.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash065.tail).map Fin.val=JHe_C_Gr_M2.Hash065.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash065.message).map Fin.val=JHe_C_Gr_M2.Hash065.message := by
  simp only [JHe_C_Gr_M2.Hash065.message,JHe_C_Gr_M2.Hash065.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash065.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash065.message=JHe_C_Gr_M2.Hash065.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash065.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash065.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash065.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash065.message,JHe_C_Gr_M2.Hash065.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash065.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash065.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash065.message=JHe_C_Gr_M2.Hash065.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash065.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨65,by omega⟩)=JHe_SHAInputs2.expected ⟨65,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash065.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H065
namespace H066
open JHe_C_Gr_M2.Hash066
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks17.B050.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks17.B051.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash066.tail).map Fin.val=JHe_C_Gr_M2.Hash066.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash066.message).map Fin.val=JHe_C_Gr_M2.Hash066.message := by
  simp only [JHe_C_Gr_M2.Hash066.message,JHe_C_Gr_M2.Hash066.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash066.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash066.message=JHe_C_Gr_M2.Hash066.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash066.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash066.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash066.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash066.message,JHe_C_Gr_M2.Hash066.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash066.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash066.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash066.message=JHe_C_Gr_M2.Hash066.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash066.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨66,by omega⟩)=JHe_SHAInputs2.expected ⟨66,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash066.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H066
namespace H067
open JHe_C_Gr_M2.Hash067
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks17.B052.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks17.B053.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash067.tail).map Fin.val=JHe_C_Gr_M2.Hash067.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash067.message).map Fin.val=JHe_C_Gr_M2.Hash067.message := by
  simp only [JHe_C_Gr_M2.Hash067.message,JHe_C_Gr_M2.Hash067.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash067.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash067.message=JHe_C_Gr_M2.Hash067.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash067.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash067.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash067.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash067.message,JHe_C_Gr_M2.Hash067.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash067.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash067.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash067.message=JHe_C_Gr_M2.Hash067.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash067.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨67,by omega⟩)=JHe_SHAInputs2.expected ⟨67,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash067.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H067
namespace H068
open JHe_C_Gr_M2.Hash068
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks17.B054.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks17.B055.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash068.tail).map Fin.val=JHe_C_Gr_M2.Hash068.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash068.message).map Fin.val=JHe_C_Gr_M2.Hash068.message := by
  simp only [JHe_C_Gr_M2.Hash068.message,JHe_C_Gr_M2.Hash068.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash068.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash068.message=JHe_C_Gr_M2.Hash068.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash068.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash068.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash068.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash068.message,JHe_C_Gr_M2.Hash068.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash068.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash068.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash068.message=JHe_C_Gr_M2.Hash068.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash068.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨68,by omega⟩)=JHe_SHAInputs2.expected ⟨68,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash068.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H068
namespace H069
open JHe_C_Gr_M2.Hash069
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks18.B000.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks18.B001.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash069.tail).map Fin.val=JHe_C_Gr_M2.Hash069.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash069.message).map Fin.val=JHe_C_Gr_M2.Hash069.message := by
  simp only [JHe_C_Gr_M2.Hash069.message,JHe_C_Gr_M2.Hash069.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash069.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash069.message=JHe_C_Gr_M2.Hash069.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash069.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash069.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash069.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash069.message,JHe_C_Gr_M2.Hash069.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash069.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash069.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash069.message=JHe_C_Gr_M2.Hash069.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash069.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨69,by omega⟩)=JHe_SHAInputs2.expected ⟨69,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash069.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H069
namespace H070
open JHe_C_Gr_M2.Hash070
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks18.B002.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks18.B003.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash070.tail).map Fin.val=JHe_C_Gr_M2.Hash070.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash070.message).map Fin.val=JHe_C_Gr_M2.Hash070.message := by
  simp only [JHe_C_Gr_M2.Hash070.message,JHe_C_Gr_M2.Hash070.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash070.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash070.message=JHe_C_Gr_M2.Hash070.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash070.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash070.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash070.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash070.message,JHe_C_Gr_M2.Hash070.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash070.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash070.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash070.message=JHe_C_Gr_M2.Hash070.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash070.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨70,by omega⟩)=JHe_SHAInputs2.expected ⟨70,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash070.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H070
namespace H071
open JHe_C_Gr_M2.Hash071
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks18.B004.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks18.B005.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash071.tail).map Fin.val=JHe_C_Gr_M2.Hash071.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash071.message).map Fin.val=JHe_C_Gr_M2.Hash071.message := by
  simp only [JHe_C_Gr_M2.Hash071.message,JHe_C_Gr_M2.Hash071.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash071.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash071.message=JHe_C_Gr_M2.Hash071.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash071.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash071.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash071.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash071.message,JHe_C_Gr_M2.Hash071.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash071.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash071.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash071.message=JHe_C_Gr_M2.Hash071.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash071.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨71,by omega⟩)=JHe_SHAInputs2.expected ⟨71,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash071.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H071
namespace H072
open JHe_C_Gr_M2.Hash072
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks18.B006.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks18.B007.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash072.tail).map Fin.val=JHe_C_Gr_M2.Hash072.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash072.message).map Fin.val=JHe_C_Gr_M2.Hash072.message := by
  simp only [JHe_C_Gr_M2.Hash072.message,JHe_C_Gr_M2.Hash072.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash072.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash072.message=JHe_C_Gr_M2.Hash072.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash072.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash072.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash072.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash072.message,JHe_C_Gr_M2.Hash072.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash072.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash072.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash072.message=JHe_C_Gr_M2.Hash072.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash072.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨72,by omega⟩)=JHe_SHAInputs2.expected ⟨72,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash072.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H072
namespace H073
open JHe_C_Gr_M2.Hash073
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks18.B008.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks18.B009.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash073.tail).map Fin.val=JHe_C_Gr_M2.Hash073.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash073.message).map Fin.val=JHe_C_Gr_M2.Hash073.message := by
  simp only [JHe_C_Gr_M2.Hash073.message,JHe_C_Gr_M2.Hash073.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash073.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash073.message=JHe_C_Gr_M2.Hash073.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash073.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash073.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash073.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash073.message,JHe_C_Gr_M2.Hash073.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash073.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash073.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash073.message=JHe_C_Gr_M2.Hash073.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash073.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨73,by omega⟩)=JHe_SHAInputs2.expected ⟨73,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash073.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H073
namespace H074
open JHe_C_Gr_M2.Hash074
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks18.B010.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks18.B011.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash074.tail).map Fin.val=JHe_C_Gr_M2.Hash074.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash074.message).map Fin.val=JHe_C_Gr_M2.Hash074.message := by
  simp only [JHe_C_Gr_M2.Hash074.message,JHe_C_Gr_M2.Hash074.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash074.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash074.message=JHe_C_Gr_M2.Hash074.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash074.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash074.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash074.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash074.message,JHe_C_Gr_M2.Hash074.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash074.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash074.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash074.message=JHe_C_Gr_M2.Hash074.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash074.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨74,by omega⟩)=JHe_SHAInputs2.expected ⟨74,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash074.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H074
namespace H075
open JHe_C_Gr_M2.Hash075
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks18.B012.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks18.B013.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash075.tail).map Fin.val=JHe_C_Gr_M2.Hash075.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash075.message).map Fin.val=JHe_C_Gr_M2.Hash075.message := by
  simp only [JHe_C_Gr_M2.Hash075.message,JHe_C_Gr_M2.Hash075.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash075.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash075.message=JHe_C_Gr_M2.Hash075.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash075.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash075.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash075.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash075.message,JHe_C_Gr_M2.Hash075.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash075.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash075.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash075.message=JHe_C_Gr_M2.Hash075.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash075.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨75,by omega⟩)=JHe_SHAInputs2.expected ⟨75,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash075.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H075
namespace H076
open JHe_C_Gr_M2.Hash076
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks18.B014.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks18.B015.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash076.tail).map Fin.val=JHe_C_Gr_M2.Hash076.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash076.message).map Fin.val=JHe_C_Gr_M2.Hash076.message := by
  simp only [JHe_C_Gr_M2.Hash076.message,JHe_C_Gr_M2.Hash076.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash076.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash076.message=JHe_C_Gr_M2.Hash076.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash076.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash076.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash076.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash076.message,JHe_C_Gr_M2.Hash076.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash076.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash076.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash076.message=JHe_C_Gr_M2.Hash076.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash076.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨76,by omega⟩)=JHe_SHAInputs2.expected ⟨76,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash076.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H076
namespace H077
open JHe_C_Gr_M2.Hash077
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks18.B016.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks18.B017.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash077.tail).map Fin.val=JHe_C_Gr_M2.Hash077.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash077.message).map Fin.val=JHe_C_Gr_M2.Hash077.message := by
  simp only [JHe_C_Gr_M2.Hash077.message,JHe_C_Gr_M2.Hash077.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash077.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash077.message=JHe_C_Gr_M2.Hash077.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash077.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash077.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash077.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash077.message,JHe_C_Gr_M2.Hash077.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash077.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash077.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash077.message=JHe_C_Gr_M2.Hash077.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash077.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨77,by omega⟩)=JHe_SHAInputs2.expected ⟨77,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash077.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H077
namespace H078
open JHe_C_Gr_M2.Hash078
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks18.B018.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks18.B019.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash078.tail).map Fin.val=JHe_C_Gr_M2.Hash078.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash078.message).map Fin.val=JHe_C_Gr_M2.Hash078.message := by
  simp only [JHe_C_Gr_M2.Hash078.message,JHe_C_Gr_M2.Hash078.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash078.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash078.message=JHe_C_Gr_M2.Hash078.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash078.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash078.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash078.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash078.message,JHe_C_Gr_M2.Hash078.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash078.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash078.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash078.message=JHe_C_Gr_M2.Hash078.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash078.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨78,by omega⟩)=JHe_SHAInputs2.expected ⟨78,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash078.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H078
namespace H079
open JHe_C_Gr_M2.Hash079
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks18.B020.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks18.B021.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash079.tail).map Fin.val=JHe_C_Gr_M2.Hash079.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash079.message).map Fin.val=JHe_C_Gr_M2.Hash079.message := by
  simp only [JHe_C_Gr_M2.Hash079.message,JHe_C_Gr_M2.Hash079.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash079.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash079.message=JHe_C_Gr_M2.Hash079.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash079.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash079.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash079.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash079.message,JHe_C_Gr_M2.Hash079.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash079.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash079.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash079.message=JHe_C_Gr_M2.Hash079.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash079.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨79,by omega⟩)=JHe_SHAInputs2.expected ⟨79,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash079.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H079
namespace H080
open JHe_C_Gr_M2.Hash080
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks18.B022.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks18.B023.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash080.tail).map Fin.val=JHe_C_Gr_M2.Hash080.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash080.message).map Fin.val=JHe_C_Gr_M2.Hash080.message := by
  simp only [JHe_C_Gr_M2.Hash080.message,JHe_C_Gr_M2.Hash080.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash080.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash080.message=JHe_C_Gr_M2.Hash080.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash080.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash080.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash080.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash080.message,JHe_C_Gr_M2.Hash080.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash080.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash080.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash080.message=JHe_C_Gr_M2.Hash080.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash080.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨80,by omega⟩)=JHe_SHAInputs2.expected ⟨80,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash080.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H080
namespace H081
open JHe_C_Gr_M2.Hash081
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks18.B024.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks18.B025.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash081.tail).map Fin.val=JHe_C_Gr_M2.Hash081.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash081.message).map Fin.val=JHe_C_Gr_M2.Hash081.message := by
  simp only [JHe_C_Gr_M2.Hash081.message,JHe_C_Gr_M2.Hash081.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash081.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash081.message=JHe_C_Gr_M2.Hash081.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash081.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash081.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash081.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash081.message,JHe_C_Gr_M2.Hash081.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash081.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash081.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash081.message=JHe_C_Gr_M2.Hash081.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash081.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨81,by omega⟩)=JHe_SHAInputs2.expected ⟨81,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash081.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H081
namespace H082
open JHe_C_Gr_M2.Hash082
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks18.B026.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks18.B027.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash082.tail).map Fin.val=JHe_C_Gr_M2.Hash082.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash082.message).map Fin.val=JHe_C_Gr_M2.Hash082.message := by
  simp only [JHe_C_Gr_M2.Hash082.message,JHe_C_Gr_M2.Hash082.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash082.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash082.message=JHe_C_Gr_M2.Hash082.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash082.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash082.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash082.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash082.message,JHe_C_Gr_M2.Hash082.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash082.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash082.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash082.message=JHe_C_Gr_M2.Hash082.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash082.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨82,by omega⟩)=JHe_SHAInputs2.expected ⟨82,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash082.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H082
namespace H083
open JHe_C_Gr_M2.Hash083
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks18.B028.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks18.B029.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash083.tail).map Fin.val=JHe_C_Gr_M2.Hash083.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash083.message).map Fin.val=JHe_C_Gr_M2.Hash083.message := by
  simp only [JHe_C_Gr_M2.Hash083.message,JHe_C_Gr_M2.Hash083.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash083.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash083.message=JHe_C_Gr_M2.Hash083.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash083.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash083.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash083.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash083.message,JHe_C_Gr_M2.Hash083.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash083.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash083.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash083.message=JHe_C_Gr_M2.Hash083.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash083.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨83,by omega⟩)=JHe_SHAInputs2.expected ⟨83,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash083.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H083
namespace H084
open JHe_C_Gr_M2.Hash084
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks18.B030.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks18.B031.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash084.tail).map Fin.val=JHe_C_Gr_M2.Hash084.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash084.message).map Fin.val=JHe_C_Gr_M2.Hash084.message := by
  simp only [JHe_C_Gr_M2.Hash084.message,JHe_C_Gr_M2.Hash084.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash084.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash084.message=JHe_C_Gr_M2.Hash084.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash084.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash084.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash084.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash084.message,JHe_C_Gr_M2.Hash084.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash084.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash084.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash084.message=JHe_C_Gr_M2.Hash084.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash084.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨84,by omega⟩)=JHe_SHAInputs2.expected ⟨84,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash084.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H084
namespace H085
open JHe_C_Gr_M2.Hash085
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks18.B032.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks18.B033.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash085.tail).map Fin.val=JHe_C_Gr_M2.Hash085.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash085.message).map Fin.val=JHe_C_Gr_M2.Hash085.message := by
  simp only [JHe_C_Gr_M2.Hash085.message,JHe_C_Gr_M2.Hash085.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash085.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash085.message=JHe_C_Gr_M2.Hash085.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash085.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash085.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash085.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash085.message,JHe_C_Gr_M2.Hash085.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash085.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash085.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash085.message=JHe_C_Gr_M2.Hash085.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash085.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨85,by omega⟩)=JHe_SHAInputs2.expected ⟨85,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash085.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H085
namespace H086
open JHe_C_Gr_M2.Hash086
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks18.B034.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks18.B035.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash086.tail).map Fin.val=JHe_C_Gr_M2.Hash086.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash086.message).map Fin.val=JHe_C_Gr_M2.Hash086.message := by
  simp only [JHe_C_Gr_M2.Hash086.message,JHe_C_Gr_M2.Hash086.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash086.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash086.message=JHe_C_Gr_M2.Hash086.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash086.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash086.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash086.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash086.message,JHe_C_Gr_M2.Hash086.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash086.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash086.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash086.message=JHe_C_Gr_M2.Hash086.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash086.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨86,by omega⟩)=JHe_SHAInputs2.expected ⟨86,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash086.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H086
namespace H087
open JHe_C_Gr_M2.Hash087
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks18.B036.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks18.B037.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash087.tail).map Fin.val=JHe_C_Gr_M2.Hash087.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash087.message).map Fin.val=JHe_C_Gr_M2.Hash087.message := by
  simp only [JHe_C_Gr_M2.Hash087.message,JHe_C_Gr_M2.Hash087.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash087.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash087.message=JHe_C_Gr_M2.Hash087.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash087.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash087.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash087.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash087.message,JHe_C_Gr_M2.Hash087.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash087.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash087.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash087.message=JHe_C_Gr_M2.Hash087.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash087.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨87,by omega⟩)=JHe_SHAInputs2.expected ⟨87,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash087.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H087
namespace H088
open JHe_C_Gr_M2.Hash088
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks18.B038.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks18.B039.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash088.tail).map Fin.val=JHe_C_Gr_M2.Hash088.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash088.message).map Fin.val=JHe_C_Gr_M2.Hash088.message := by
  simp only [JHe_C_Gr_M2.Hash088.message,JHe_C_Gr_M2.Hash088.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash088.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash088.message=JHe_C_Gr_M2.Hash088.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash088.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash088.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash088.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash088.message,JHe_C_Gr_M2.Hash088.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash088.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash088.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash088.message=JHe_C_Gr_M2.Hash088.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash088.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨88,by omega⟩)=JHe_SHAInputs2.expected ⟨88,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash088.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H088
namespace H089
open JHe_C_Gr_M2.Hash089
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks18.B040.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks18.B041.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash089.tail).map Fin.val=JHe_C_Gr_M2.Hash089.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash089.message).map Fin.val=JHe_C_Gr_M2.Hash089.message := by
  simp only [JHe_C_Gr_M2.Hash089.message,JHe_C_Gr_M2.Hash089.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash089.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash089.message=JHe_C_Gr_M2.Hash089.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash089.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash089.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash089.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash089.message,JHe_C_Gr_M2.Hash089.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash089.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash089.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash089.message=JHe_C_Gr_M2.Hash089.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash089.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨89,by omega⟩)=JHe_SHAInputs2.expected ⟨89,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash089.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H089
namespace H090
open JHe_C_Gr_M2.Hash090
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks18.B042.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks18.B043.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash090.tail).map Fin.val=JHe_C_Gr_M2.Hash090.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash090.message).map Fin.val=JHe_C_Gr_M2.Hash090.message := by
  simp only [JHe_C_Gr_M2.Hash090.message,JHe_C_Gr_M2.Hash090.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash090.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash090.message=JHe_C_Gr_M2.Hash090.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash090.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash090.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash090.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash090.message,JHe_C_Gr_M2.Hash090.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash090.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash090.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash090.message=JHe_C_Gr_M2.Hash090.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash090.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨90,by omega⟩)=JHe_SHAInputs2.expected ⟨90,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash090.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H090
namespace H091
open JHe_C_Gr_M2.Hash091
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks18.B044.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks18.B045.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash091.tail).map Fin.val=JHe_C_Gr_M2.Hash091.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash091.message).map Fin.val=JHe_C_Gr_M2.Hash091.message := by
  simp only [JHe_C_Gr_M2.Hash091.message,JHe_C_Gr_M2.Hash091.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash091.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash091.message=JHe_C_Gr_M2.Hash091.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash091.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash091.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash091.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash091.message,JHe_C_Gr_M2.Hash091.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash091.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash091.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash091.message=JHe_C_Gr_M2.Hash091.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash091.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨91,by omega⟩)=JHe_SHAInputs2.expected ⟨91,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash091.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H091
namespace H092
open JHe_C_Gr_M2.Hash092
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks18.B046.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks18.B047.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash092.tail).map Fin.val=JHe_C_Gr_M2.Hash092.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash092.message).map Fin.val=JHe_C_Gr_M2.Hash092.message := by
  simp only [JHe_C_Gr_M2.Hash092.message,JHe_C_Gr_M2.Hash092.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash092.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash092.message=JHe_C_Gr_M2.Hash092.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash092.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash092.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash092.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash092.message,JHe_C_Gr_M2.Hash092.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash092.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash092.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash092.message=JHe_C_Gr_M2.Hash092.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash092.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨92,by omega⟩)=JHe_SHAInputs2.expected ⟨92,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash092.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H092
namespace H093
open JHe_C_Gr_M2.Hash093
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks18.B048.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks18.B049.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash093.tail).map Fin.val=JHe_C_Gr_M2.Hash093.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash093.message).map Fin.val=JHe_C_Gr_M2.Hash093.message := by
  simp only [JHe_C_Gr_M2.Hash093.message,JHe_C_Gr_M2.Hash093.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash093.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash093.message=JHe_C_Gr_M2.Hash093.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash093.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash093.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash093.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash093.message,JHe_C_Gr_M2.Hash093.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash093.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash093.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash093.message=JHe_C_Gr_M2.Hash093.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash093.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨93,by omega⟩)=JHe_SHAInputs2.expected ⟨93,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash093.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H093
namespace H094
open JHe_C_Gr_M2.Hash094
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks18.B050.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks18.B051.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash094.tail).map Fin.val=JHe_C_Gr_M2.Hash094.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash094.message).map Fin.val=JHe_C_Gr_M2.Hash094.message := by
  simp only [JHe_C_Gr_M2.Hash094.message,JHe_C_Gr_M2.Hash094.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash094.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash094.message=JHe_C_Gr_M2.Hash094.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash094.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash094.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash094.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash094.message,JHe_C_Gr_M2.Hash094.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash094.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash094.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash094.message=JHe_C_Gr_M2.Hash094.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash094.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨94,by omega⟩)=JHe_SHAInputs2.expected ⟨94,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash094.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H094
namespace H095
open JHe_C_Gr_M2.Hash095
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks18.B052.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks18.B053.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash095.tail).map Fin.val=JHe_C_Gr_M2.Hash095.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash095.message).map Fin.val=JHe_C_Gr_M2.Hash095.message := by
  simp only [JHe_C_Gr_M2.Hash095.message,JHe_C_Gr_M2.Hash095.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash095.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash095.message=JHe_C_Gr_M2.Hash095.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash095.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash095.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash095.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash095.message,JHe_C_Gr_M2.Hash095.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash095.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash095.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash095.message=JHe_C_Gr_M2.Hash095.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash095.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨95,by omega⟩)=JHe_SHAInputs2.expected ⟨95,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash095.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H095
end AspisR1.JHx_T2C02
