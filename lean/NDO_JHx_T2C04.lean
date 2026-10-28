import NDO_JHx_Blocks20
import NDO_JHe_SHAEquations2
import NDO_JGz_HashTools
set_option autoImplicit false
namespace AspisR1.JHx_T2C04
open JFp_SHA256
namespace H128
open JGc_TX2_M2.Hash154
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks20.B006.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks20.B007.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash154.tail).map Fin.val=JGc_TX2_M2.Hash154.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash154.message).map Fin.val=JGc_TX2_M2.Hash154.message := by
  simp only [JGc_TX2_M2.Hash154.message,JGc_TX2_M2.Hash154.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JGc_TX2_M2.Hash154.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JGc_TX2_M2.Hash154.message=JGc_TX2_M2.Hash154.chunks.flatten := by
  have size : JGc_TX2_M2.Hash154.message.length=65 := by
    simp only [JGc_TX2_M2.Hash154.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JGc_TX2_M2.Hash154.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JGc_TX2_M2.Hash154.message,JGc_TX2_M2.Hash154.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JGc_TX2_M2.Hash154.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JGc_TX2_M2.Hash154.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JGc_TX2_M2.Hash154.message=JGc_TX2_M2.Hash154.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JGc_TX2_M2.Hash154.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨128,by omega⟩)=JHe_SHAInputs2.expected ⟨128,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash154.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H128
namespace H129
open JGc_TX2_M2.Hash155
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks20.B008.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks20.B009.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash155.tail).map Fin.val=JGc_TX2_M2.Hash155.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash155.message).map Fin.val=JGc_TX2_M2.Hash155.message := by
  simp only [JGc_TX2_M2.Hash155.message,JGc_TX2_M2.Hash155.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JGc_TX2_M2.Hash155.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JGc_TX2_M2.Hash155.message=JGc_TX2_M2.Hash155.chunks.flatten := by
  have size : JGc_TX2_M2.Hash155.message.length=65 := by
    simp only [JGc_TX2_M2.Hash155.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JGc_TX2_M2.Hash155.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JGc_TX2_M2.Hash155.message,JGc_TX2_M2.Hash155.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JGc_TX2_M2.Hash155.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JGc_TX2_M2.Hash155.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JGc_TX2_M2.Hash155.message=JGc_TX2_M2.Hash155.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JGc_TX2_M2.Hash155.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨129,by omega⟩)=JHe_SHAInputs2.expected ⟨129,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash155.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H129
namespace H130
open JHe_C_Gr_M2.Hash130
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks20.B010.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks20.B011.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash130.tail).map Fin.val=JHe_C_Gr_M2.Hash130.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash130.message).map Fin.val=JHe_C_Gr_M2.Hash130.message := by
  simp only [JHe_C_Gr_M2.Hash130.message,JHe_C_Gr_M2.Hash130.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash130.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash130.message=JHe_C_Gr_M2.Hash130.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash130.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash130.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash130.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash130.message,JHe_C_Gr_M2.Hash130.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash130.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash130.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash130.message=JHe_C_Gr_M2.Hash130.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash130.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨130,by omega⟩)=JHe_SHAInputs2.expected ⟨130,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash130.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H130
namespace H131
open JHe_C_Gr_M2.Hash131
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks20.B012.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks20.B013.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash131.tail).map Fin.val=JHe_C_Gr_M2.Hash131.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash131.message).map Fin.val=JHe_C_Gr_M2.Hash131.message := by
  simp only [JHe_C_Gr_M2.Hash131.message,JHe_C_Gr_M2.Hash131.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M2.Hash131.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M2.Hash131.message=JHe_C_Gr_M2.Hash131.chunks.flatten := by
  have size : JHe_C_Gr_M2.Hash131.message.length=65 := by
    simp only [JHe_C_Gr_M2.Hash131.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M2.Hash131.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M2.Hash131.message,JHe_C_Gr_M2.Hash131.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M2.Hash131.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M2.Hash131.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M2.Hash131.message=JHe_C_Gr_M2.Hash131.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M2.Hash131.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨131,by omega⟩)=JHe_SHAInputs2.expected ⟨131,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M2.Hash131.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H131
namespace H132
open JGc_TX2_M2.Hash157
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks20.B014.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks20.B015.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash157.tail).map Fin.val=JGc_TX2_M2.Hash157.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash157.message).map Fin.val=JGc_TX2_M2.Hash157.message := by
  simp only [JGc_TX2_M2.Hash157.message,JGc_TX2_M2.Hash157.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JGc_TX2_M2.Hash157.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JGc_TX2_M2.Hash157.message=JGc_TX2_M2.Hash157.chunks.flatten := by
  have size : JGc_TX2_M2.Hash157.message.length=65 := by
    simp only [JGc_TX2_M2.Hash157.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JGc_TX2_M2.Hash157.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JGc_TX2_M2.Hash157.message,JGc_TX2_M2.Hash157.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JGc_TX2_M2.Hash157.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JGc_TX2_M2.Hash157.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JGc_TX2_M2.Hash157.message=JGc_TX2_M2.Hash157.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JGc_TX2_M2.Hash157.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨132,by omega⟩)=JHe_SHAInputs2.expected ⟨132,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash157.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H132
namespace H133
open JGc_TX2_M2.Hash158
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks20.B016.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks20.B017.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash158.tail).map Fin.val=JGc_TX2_M2.Hash158.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash158.message).map Fin.val=JGc_TX2_M2.Hash158.message := by
  simp only [JGc_TX2_M2.Hash158.message,JGc_TX2_M2.Hash158.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JGc_TX2_M2.Hash158.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JGc_TX2_M2.Hash158.message=JGc_TX2_M2.Hash158.chunks.flatten := by
  have size : JGc_TX2_M2.Hash158.message.length=65 := by
    simp only [JGc_TX2_M2.Hash158.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JGc_TX2_M2.Hash158.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JGc_TX2_M2.Hash158.message,JGc_TX2_M2.Hash158.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JGc_TX2_M2.Hash158.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JGc_TX2_M2.Hash158.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JGc_TX2_M2.Hash158.message=JGc_TX2_M2.Hash158.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JGc_TX2_M2.Hash158.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨133,by omega⟩)=JHe_SHAInputs2.expected ⟨133,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash158.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H133
namespace H134
open JGc_TX2_M2.Hash159
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks20.B018.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks20.B019.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash159.tail).map Fin.val=JGc_TX2_M2.Hash159.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash159.message).map Fin.val=JGc_TX2_M2.Hash159.message := by
  simp only [JGc_TX2_M2.Hash159.message,JGc_TX2_M2.Hash159.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JGc_TX2_M2.Hash159.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JGc_TX2_M2.Hash159.message=JGc_TX2_M2.Hash159.chunks.flatten := by
  have size : JGc_TX2_M2.Hash159.message.length=65 := by
    simp only [JGc_TX2_M2.Hash159.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JGc_TX2_M2.Hash159.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JGc_TX2_M2.Hash159.message,JGc_TX2_M2.Hash159.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JGc_TX2_M2.Hash159.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JGc_TX2_M2.Hash159.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JGc_TX2_M2.Hash159.message=JGc_TX2_M2.Hash159.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JGc_TX2_M2.Hash159.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨134,by omega⟩)=JHe_SHAInputs2.expected ⟨134,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash159.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H134
namespace H135
open JGc_TX2_M2.Hash160
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks20.B020.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks20.B021.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash160.tail).map Fin.val=JGc_TX2_M2.Hash160.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash160.message).map Fin.val=JGc_TX2_M2.Hash160.message := by
  simp only [JGc_TX2_M2.Hash160.message,JGc_TX2_M2.Hash160.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JGc_TX2_M2.Hash160.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JGc_TX2_M2.Hash160.message=JGc_TX2_M2.Hash160.chunks.flatten := by
  have size : JGc_TX2_M2.Hash160.message.length=65 := by
    simp only [JGc_TX2_M2.Hash160.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JGc_TX2_M2.Hash160.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JGc_TX2_M2.Hash160.message,JGc_TX2_M2.Hash160.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JGc_TX2_M2.Hash160.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JGc_TX2_M2.Hash160.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JGc_TX2_M2.Hash160.message=JGc_TX2_M2.Hash160.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JGc_TX2_M2.Hash160.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨135,by omega⟩)=JHe_SHAInputs2.expected ⟨135,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash160.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H135
namespace H136
open JGc_TX2_M2.Hash161
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks20.B022.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks20.B023.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash161.tail).map Fin.val=JGc_TX2_M2.Hash161.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash161.message).map Fin.val=JGc_TX2_M2.Hash161.message := by
  simp only [JGc_TX2_M2.Hash161.message,JGc_TX2_M2.Hash161.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JGc_TX2_M2.Hash161.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JGc_TX2_M2.Hash161.message=JGc_TX2_M2.Hash161.chunks.flatten := by
  have size : JGc_TX2_M2.Hash161.message.length=65 := by
    simp only [JGc_TX2_M2.Hash161.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JGc_TX2_M2.Hash161.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JGc_TX2_M2.Hash161.message,JGc_TX2_M2.Hash161.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JGc_TX2_M2.Hash161.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JGc_TX2_M2.Hash161.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JGc_TX2_M2.Hash161.message=JGc_TX2_M2.Hash161.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JGc_TX2_M2.Hash161.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨136,by omega⟩)=JHe_SHAInputs2.expected ⟨136,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash161.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H136
namespace H137
open JGc_TX2_M2.Hash162
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks20.B024.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks20.B025.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash162.tail).map Fin.val=JGc_TX2_M2.Hash162.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash162.message).map Fin.val=JGc_TX2_M2.Hash162.message := by
  simp only [JGc_TX2_M2.Hash162.message,JGc_TX2_M2.Hash162.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JGc_TX2_M2.Hash162.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JGc_TX2_M2.Hash162.message=JGc_TX2_M2.Hash162.chunks.flatten := by
  have size : JGc_TX2_M2.Hash162.message.length=65 := by
    simp only [JGc_TX2_M2.Hash162.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JGc_TX2_M2.Hash162.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JGc_TX2_M2.Hash162.message,JGc_TX2_M2.Hash162.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JGc_TX2_M2.Hash162.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JGc_TX2_M2.Hash162.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JGc_TX2_M2.Hash162.message=JGc_TX2_M2.Hash162.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JGc_TX2_M2.Hash162.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨137,by omega⟩)=JHe_SHAInputs2.expected ⟨137,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash162.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H137
namespace H138
open JGc_TX2_M2.Hash163
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks20.B026.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks20.B027.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash163.tail).map Fin.val=JGc_TX2_M2.Hash163.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash163.message).map Fin.val=JGc_TX2_M2.Hash163.message := by
  simp only [JGc_TX2_M2.Hash163.message,JGc_TX2_M2.Hash163.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JGc_TX2_M2.Hash163.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JGc_TX2_M2.Hash163.message=JGc_TX2_M2.Hash163.chunks.flatten := by
  have size : JGc_TX2_M2.Hash163.message.length=65 := by
    simp only [JGc_TX2_M2.Hash163.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JGc_TX2_M2.Hash163.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JGc_TX2_M2.Hash163.message,JGc_TX2_M2.Hash163.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JGc_TX2_M2.Hash163.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JGc_TX2_M2.Hash163.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JGc_TX2_M2.Hash163.message=JGc_TX2_M2.Hash163.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JGc_TX2_M2.Hash163.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs2.input ⟨138,by omega⟩)=JHe_SHAInputs2.expected ⟨138,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash163.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H138
end AspisR1.JHx_T2C04
