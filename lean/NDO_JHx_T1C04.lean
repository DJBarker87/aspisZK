import NDO_JHx_Blocks14
import NDO_JHx_Blocks15
import NDO_JHe_SHAEquations1
import NDO_JGz_HashTools
set_option autoImplicit false
namespace AspisR1.JHx_T1C04
open JFp_SHA256
namespace H128
open JHe_C_Gr_M1.Hash128
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks14.B018.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks14.B019.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash128.tail).map Fin.val=JHe_C_Gr_M1.Hash128.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash128.message).map Fin.val=JHe_C_Gr_M1.Hash128.message := by
  simp only [JHe_C_Gr_M1.Hash128.message,JHe_C_Gr_M1.Hash128.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash128.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash128.message=JHe_C_Gr_M1.Hash128.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash128.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash128.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash128.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash128.message,JHe_C_Gr_M1.Hash128.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash128.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash128.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash128.message=JHe_C_Gr_M1.Hash128.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash128.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨128,by omega⟩)=JHe_SHAInputs1.expected ⟨128,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash128.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H128
namespace H129
open JHe_C_Gr_M1.Hash129
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks14.B020.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks14.B021.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash129.tail).map Fin.val=JHe_C_Gr_M1.Hash129.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash129.message).map Fin.val=JHe_C_Gr_M1.Hash129.message := by
  simp only [JHe_C_Gr_M1.Hash129.message,JHe_C_Gr_M1.Hash129.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash129.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash129.message=JHe_C_Gr_M1.Hash129.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash129.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash129.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash129.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash129.message,JHe_C_Gr_M1.Hash129.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash129.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash129.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash129.message=JHe_C_Gr_M1.Hash129.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash129.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨129,by omega⟩)=JHe_SHAInputs1.expected ⟨129,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash129.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H129
namespace H130
open JHe_C_Gr_M1.Hash130
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks14.B022.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks14.B023.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash130.tail).map Fin.val=JHe_C_Gr_M1.Hash130.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash130.message).map Fin.val=JHe_C_Gr_M1.Hash130.message := by
  simp only [JHe_C_Gr_M1.Hash130.message,JHe_C_Gr_M1.Hash130.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash130.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash130.message=JHe_C_Gr_M1.Hash130.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash130.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash130.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash130.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash130.message,JHe_C_Gr_M1.Hash130.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash130.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash130.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash130.message=JHe_C_Gr_M1.Hash130.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash130.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨130,by omega⟩)=JHe_SHAInputs1.expected ⟨130,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash130.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H130
namespace H131
open JHe_C_Gr_M1.Hash131
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks14.B024.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks14.B025.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash131.tail).map Fin.val=JHe_C_Gr_M1.Hash131.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash131.message).map Fin.val=JHe_C_Gr_M1.Hash131.message := by
  simp only [JHe_C_Gr_M1.Hash131.message,JHe_C_Gr_M1.Hash131.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash131.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash131.message=JHe_C_Gr_M1.Hash131.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash131.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash131.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash131.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash131.message,JHe_C_Gr_M1.Hash131.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash131.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash131.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash131.message=JHe_C_Gr_M1.Hash131.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash131.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨131,by omega⟩)=JHe_SHAInputs1.expected ⟨131,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash131.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H131
namespace H132
open JGh_TX2_M1.Hash161
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks14.B026.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks14.B027.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash161.tail).map Fin.val=JGh_TX2_M1.Hash161.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash161.message).map Fin.val=JGh_TX2_M1.Hash161.message := by
  simp only [JGh_TX2_M1.Hash161.message,JGh_TX2_M1.Hash161.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JGh_TX2_M1.Hash161.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JGh_TX2_M1.Hash161.message=JGh_TX2_M1.Hash161.chunks.flatten := by
  have size : JGh_TX2_M1.Hash161.message.length=65 := by
    simp only [JGh_TX2_M1.Hash161.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JGh_TX2_M1.Hash161.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JGh_TX2_M1.Hash161.message,JGh_TX2_M1.Hash161.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JGh_TX2_M1.Hash161.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JGh_TX2_M1.Hash161.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JGh_TX2_M1.Hash161.message=JGh_TX2_M1.Hash161.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JGh_TX2_M1.Hash161.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨132,by omega⟩)=JHe_SHAInputs1.expected ⟨132,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash161.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H132
namespace H133
open JHe_C_Gr_M1.Hash133
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks14.B028.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks14.B029.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash133.tail).map Fin.val=JHe_C_Gr_M1.Hash133.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash133.message).map Fin.val=JHe_C_Gr_M1.Hash133.message := by
  simp only [JHe_C_Gr_M1.Hash133.message,JHe_C_Gr_M1.Hash133.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash133.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash133.message=JHe_C_Gr_M1.Hash133.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash133.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash133.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash133.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash133.message,JHe_C_Gr_M1.Hash133.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash133.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash133.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash133.message=JHe_C_Gr_M1.Hash133.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash133.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨133,by omega⟩)=JHe_SHAInputs1.expected ⟨133,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash133.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H133
namespace H134
open JGh_TX2_M1.Hash164
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks14.B030.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks14.B031.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash164.tail).map Fin.val=JGh_TX2_M1.Hash164.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash164.message).map Fin.val=JGh_TX2_M1.Hash164.message := by
  simp only [JGh_TX2_M1.Hash164.message,JGh_TX2_M1.Hash164.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JGh_TX2_M1.Hash164.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JGh_TX2_M1.Hash164.message=JGh_TX2_M1.Hash164.chunks.flatten := by
  have size : JGh_TX2_M1.Hash164.message.length=65 := by
    simp only [JGh_TX2_M1.Hash164.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JGh_TX2_M1.Hash164.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JGh_TX2_M1.Hash164.message,JGh_TX2_M1.Hash164.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JGh_TX2_M1.Hash164.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JGh_TX2_M1.Hash164.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JGh_TX2_M1.Hash164.message=JGh_TX2_M1.Hash164.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JGh_TX2_M1.Hash164.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨134,by omega⟩)=JHe_SHAInputs1.expected ⟨134,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash164.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H134
namespace H135
open JHe_C_Gr_M1.Hash135
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks14.B032.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks14.B033.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash135.tail).map Fin.val=JHe_C_Gr_M1.Hash135.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash135.message).map Fin.val=JHe_C_Gr_M1.Hash135.message := by
  simp only [JHe_C_Gr_M1.Hash135.message,JHe_C_Gr_M1.Hash135.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash135.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash135.message=JHe_C_Gr_M1.Hash135.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash135.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash135.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash135.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash135.message,JHe_C_Gr_M1.Hash135.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash135.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash135.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash135.message=JHe_C_Gr_M1.Hash135.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash135.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨135,by omega⟩)=JHe_SHAInputs1.expected ⟨135,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash135.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H135
namespace H136
open JHe_C_Gr_M1.Hash136
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks14.B034.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks14.B035.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash136.tail).map Fin.val=JHe_C_Gr_M1.Hash136.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash136.message).map Fin.val=JHe_C_Gr_M1.Hash136.message := by
  simp only [JHe_C_Gr_M1.Hash136.message,JHe_C_Gr_M1.Hash136.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash136.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash136.message=JHe_C_Gr_M1.Hash136.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash136.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash136.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash136.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash136.message,JHe_C_Gr_M1.Hash136.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash136.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash136.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash136.message=JHe_C_Gr_M1.Hash136.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash136.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨136,by omega⟩)=JHe_SHAInputs1.expected ⟨136,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash136.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H136
namespace H137
open JGh_TX2_M1.Hash165
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks14.B036.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks14.B037.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash165.tail).map Fin.val=JGh_TX2_M1.Hash165.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash165.message).map Fin.val=JGh_TX2_M1.Hash165.message := by
  simp only [JGh_TX2_M1.Hash165.message,JGh_TX2_M1.Hash165.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JGh_TX2_M1.Hash165.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JGh_TX2_M1.Hash165.message=JGh_TX2_M1.Hash165.chunks.flatten := by
  have size : JGh_TX2_M1.Hash165.message.length=65 := by
    simp only [JGh_TX2_M1.Hash165.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JGh_TX2_M1.Hash165.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JGh_TX2_M1.Hash165.message,JGh_TX2_M1.Hash165.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JGh_TX2_M1.Hash165.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JGh_TX2_M1.Hash165.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JGh_TX2_M1.Hash165.message=JGh_TX2_M1.Hash165.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JGh_TX2_M1.Hash165.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨137,by omega⟩)=JHe_SHAInputs1.expected ⟨137,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash165.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H137
namespace H138
open JHe_C_Gr_M1.Hash138
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks14.B038.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks14.B039.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash138.tail).map Fin.val=JHe_C_Gr_M1.Hash138.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash138.message).map Fin.val=JHe_C_Gr_M1.Hash138.message := by
  simp only [JHe_C_Gr_M1.Hash138.message,JHe_C_Gr_M1.Hash138.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash138.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash138.message=JHe_C_Gr_M1.Hash138.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash138.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash138.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash138.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash138.message,JHe_C_Gr_M1.Hash138.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash138.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash138.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash138.message=JHe_C_Gr_M1.Hash138.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash138.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨138,by omega⟩)=JHe_SHAInputs1.expected ⟨138,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash138.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H138
namespace H139
open JHe_C_Gr_M1.Hash139
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks14.B040.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks14.B041.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash139.tail).map Fin.val=JHe_C_Gr_M1.Hash139.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash139.message).map Fin.val=JHe_C_Gr_M1.Hash139.message := by
  simp only [JHe_C_Gr_M1.Hash139.message,JHe_C_Gr_M1.Hash139.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash139.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash139.message=JHe_C_Gr_M1.Hash139.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash139.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash139.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash139.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash139.message,JHe_C_Gr_M1.Hash139.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash139.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash139.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash139.message=JHe_C_Gr_M1.Hash139.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash139.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨139,by omega⟩)=JHe_SHAInputs1.expected ⟨139,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash139.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H139
namespace H140
open JHe_C_Gr_M1.Hash140
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks14.B042.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks14.B043.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash140.tail).map Fin.val=JHe_C_Gr_M1.Hash140.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash140.message).map Fin.val=JHe_C_Gr_M1.Hash140.message := by
  simp only [JHe_C_Gr_M1.Hash140.message,JHe_C_Gr_M1.Hash140.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash140.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash140.message=JHe_C_Gr_M1.Hash140.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash140.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash140.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash140.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash140.message,JHe_C_Gr_M1.Hash140.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash140.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash140.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash140.message=JHe_C_Gr_M1.Hash140.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash140.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨140,by omega⟩)=JHe_SHAInputs1.expected ⟨140,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash140.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H140
namespace H141
open JGh_TX2_M1.Hash171
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks14.B044.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks14.B045.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash171.tail).map Fin.val=JGh_TX2_M1.Hash171.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash171.message).map Fin.val=JGh_TX2_M1.Hash171.message := by
  simp only [JGh_TX2_M1.Hash171.message,JGh_TX2_M1.Hash171.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JGh_TX2_M1.Hash171.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JGh_TX2_M1.Hash171.message=JGh_TX2_M1.Hash171.chunks.flatten := by
  have size : JGh_TX2_M1.Hash171.message.length=65 := by
    simp only [JGh_TX2_M1.Hash171.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JGh_TX2_M1.Hash171.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JGh_TX2_M1.Hash171.message,JGh_TX2_M1.Hash171.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JGh_TX2_M1.Hash171.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JGh_TX2_M1.Hash171.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JGh_TX2_M1.Hash171.message=JGh_TX2_M1.Hash171.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JGh_TX2_M1.Hash171.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨141,by omega⟩)=JHe_SHAInputs1.expected ⟨141,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash171.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H141
namespace H142
open JGh_TX2_M1.Hash173
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks14.B046.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks14.B047.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash173.tail).map Fin.val=JGh_TX2_M1.Hash173.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash173.message).map Fin.val=JGh_TX2_M1.Hash173.message := by
  simp only [JGh_TX2_M1.Hash173.message,JGh_TX2_M1.Hash173.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JGh_TX2_M1.Hash173.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JGh_TX2_M1.Hash173.message=JGh_TX2_M1.Hash173.chunks.flatten := by
  have size : JGh_TX2_M1.Hash173.message.length=65 := by
    simp only [JGh_TX2_M1.Hash173.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JGh_TX2_M1.Hash173.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JGh_TX2_M1.Hash173.message,JGh_TX2_M1.Hash173.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JGh_TX2_M1.Hash173.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JGh_TX2_M1.Hash173.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JGh_TX2_M1.Hash173.message=JGh_TX2_M1.Hash173.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JGh_TX2_M1.Hash173.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨142,by omega⟩)=JHe_SHAInputs1.expected ⟨142,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash173.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H142
namespace H143
open JHe_C_Gr_M1.Hash143
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks14.B048.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks14.B049.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash143.tail).map Fin.val=JHe_C_Gr_M1.Hash143.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash143.message).map Fin.val=JHe_C_Gr_M1.Hash143.message := by
  simp only [JHe_C_Gr_M1.Hash143.message,JHe_C_Gr_M1.Hash143.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash143.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash143.message=JHe_C_Gr_M1.Hash143.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash143.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash143.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash143.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash143.message,JHe_C_Gr_M1.Hash143.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash143.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash143.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash143.message=JHe_C_Gr_M1.Hash143.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash143.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨143,by omega⟩)=JHe_SHAInputs1.expected ⟨143,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash143.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H143
namespace H144
open JGh_TX2_M1.Hash174
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks14.B050.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks14.B051.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash174.tail).map Fin.val=JGh_TX2_M1.Hash174.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash174.message).map Fin.val=JGh_TX2_M1.Hash174.message := by
  simp only [JGh_TX2_M1.Hash174.message,JGh_TX2_M1.Hash174.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JGh_TX2_M1.Hash174.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JGh_TX2_M1.Hash174.message=JGh_TX2_M1.Hash174.chunks.flatten := by
  have size : JGh_TX2_M1.Hash174.message.length=65 := by
    simp only [JGh_TX2_M1.Hash174.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JGh_TX2_M1.Hash174.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JGh_TX2_M1.Hash174.message,JGh_TX2_M1.Hash174.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JGh_TX2_M1.Hash174.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JGh_TX2_M1.Hash174.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JGh_TX2_M1.Hash174.message=JGh_TX2_M1.Hash174.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JGh_TX2_M1.Hash174.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨144,by omega⟩)=JHe_SHAInputs1.expected ⟨144,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash174.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H144
namespace H145
open JHe_C_Gr_M1.Hash145
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks14.B052.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks14.B053.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash145.tail).map Fin.val=JHe_C_Gr_M1.Hash145.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash145.message).map Fin.val=JHe_C_Gr_M1.Hash145.message := by
  simp only [JHe_C_Gr_M1.Hash145.message,JHe_C_Gr_M1.Hash145.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash145.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash145.message=JHe_C_Gr_M1.Hash145.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash145.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash145.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash145.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash145.message,JHe_C_Gr_M1.Hash145.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash145.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash145.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash145.message=JHe_C_Gr_M1.Hash145.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash145.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨145,by omega⟩)=JHe_SHAInputs1.expected ⟨145,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash145.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H145
namespace H146
open JHe_C_Gr_M1.Hash146
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks14.B054.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks14.B055.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash146.tail).map Fin.val=JHe_C_Gr_M1.Hash146.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash146.message).map Fin.val=JHe_C_Gr_M1.Hash146.message := by
  simp only [JHe_C_Gr_M1.Hash146.message,JHe_C_Gr_M1.Hash146.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash146.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash146.message=JHe_C_Gr_M1.Hash146.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash146.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash146.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash146.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash146.message,JHe_C_Gr_M1.Hash146.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash146.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash146.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash146.message=JHe_C_Gr_M1.Hash146.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash146.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨146,by omega⟩)=JHe_SHAInputs1.expected ⟨146,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash146.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H146
namespace H147
open JGh_TX2_M1.Hash177
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks15.B000.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks15.B001.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash177.tail).map Fin.val=JGh_TX2_M1.Hash177.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash177.message).map Fin.val=JGh_TX2_M1.Hash177.message := by
  simp only [JGh_TX2_M1.Hash177.message,JGh_TX2_M1.Hash177.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JGh_TX2_M1.Hash177.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JGh_TX2_M1.Hash177.message=JGh_TX2_M1.Hash177.chunks.flatten := by
  have size : JGh_TX2_M1.Hash177.message.length=65 := by
    simp only [JGh_TX2_M1.Hash177.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JGh_TX2_M1.Hash177.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JGh_TX2_M1.Hash177.message,JGh_TX2_M1.Hash177.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JGh_TX2_M1.Hash177.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JGh_TX2_M1.Hash177.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JGh_TX2_M1.Hash177.message=JGh_TX2_M1.Hash177.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JGh_TX2_M1.Hash177.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨147,by omega⟩)=JHe_SHAInputs1.expected ⟨147,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash177.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H147
namespace H148
open JGh_TX2_M1.Hash178
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks15.B002.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks15.B003.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash178.tail).map Fin.val=JGh_TX2_M1.Hash178.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash178.message).map Fin.val=JGh_TX2_M1.Hash178.message := by
  simp only [JGh_TX2_M1.Hash178.message,JGh_TX2_M1.Hash178.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JGh_TX2_M1.Hash178.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JGh_TX2_M1.Hash178.message=JGh_TX2_M1.Hash178.chunks.flatten := by
  have size : JGh_TX2_M1.Hash178.message.length=65 := by
    simp only [JGh_TX2_M1.Hash178.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JGh_TX2_M1.Hash178.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JGh_TX2_M1.Hash178.message,JGh_TX2_M1.Hash178.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JGh_TX2_M1.Hash178.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JGh_TX2_M1.Hash178.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JGh_TX2_M1.Hash178.message=JGh_TX2_M1.Hash178.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JGh_TX2_M1.Hash178.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨148,by omega⟩)=JHe_SHAInputs1.expected ⟨148,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash178.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H148
namespace H149
open JGh_TX2_M1.Hash179
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks15.B004.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks15.B005.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash179.tail).map Fin.val=JGh_TX2_M1.Hash179.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash179.message).map Fin.val=JGh_TX2_M1.Hash179.message := by
  simp only [JGh_TX2_M1.Hash179.message,JGh_TX2_M1.Hash179.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JGh_TX2_M1.Hash179.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JGh_TX2_M1.Hash179.message=JGh_TX2_M1.Hash179.chunks.flatten := by
  have size : JGh_TX2_M1.Hash179.message.length=65 := by
    simp only [JGh_TX2_M1.Hash179.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JGh_TX2_M1.Hash179.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JGh_TX2_M1.Hash179.message,JGh_TX2_M1.Hash179.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JGh_TX2_M1.Hash179.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JGh_TX2_M1.Hash179.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JGh_TX2_M1.Hash179.message=JGh_TX2_M1.Hash179.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JGh_TX2_M1.Hash179.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨149,by omega⟩)=JHe_SHAInputs1.expected ⟨149,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash179.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H149
namespace H150
open JHe_C_Gr_M1.Hash150
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks15.B006.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks15.B007.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash150.tail).map Fin.val=JHe_C_Gr_M1.Hash150.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash150.message).map Fin.val=JHe_C_Gr_M1.Hash150.message := by
  simp only [JHe_C_Gr_M1.Hash150.message,JHe_C_Gr_M1.Hash150.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash150.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash150.message=JHe_C_Gr_M1.Hash150.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash150.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash150.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash150.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash150.message,JHe_C_Gr_M1.Hash150.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash150.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash150.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash150.message=JHe_C_Gr_M1.Hash150.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash150.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨150,by omega⟩)=JHe_SHAInputs1.expected ⟨150,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash150.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H150
namespace H151
open JHe_C_Gr_M1.Hash151
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks15.B008.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks15.B009.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash151.tail).map Fin.val=JHe_C_Gr_M1.Hash151.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash151.message).map Fin.val=JHe_C_Gr_M1.Hash151.message := by
  simp only [JHe_C_Gr_M1.Hash151.message,JHe_C_Gr_M1.Hash151.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash151.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JHe_C_Gr_M1.Hash151.message=JHe_C_Gr_M1.Hash151.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash151.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash151.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash151.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash151.message,JHe_C_Gr_M1.Hash151.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash151.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash151.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash151.message=JHe_C_Gr_M1.Hash151.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash151.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨151,by omega⟩)=JHe_SHAInputs1.expected ⟨151,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash151.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H151
namespace H152
open JGh_TX2_M1.Hash181
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks15.B010.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks15.B011.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash181.tail).map Fin.val=JGh_TX2_M1.Hash181.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash181.message).map Fin.val=JGh_TX2_M1.Hash181.message := by
  simp only [JGh_TX2_M1.Hash181.message,JGh_TX2_M1.Hash181.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JGh_TX2_M1.Hash181.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JGh_TX2_M1.Hash181.message=JGh_TX2_M1.Hash181.chunks.flatten := by
  have size : JGh_TX2_M1.Hash181.message.length=65 := by
    simp only [JGh_TX2_M1.Hash181.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JGh_TX2_M1.Hash181.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JGh_TX2_M1.Hash181.message,JGh_TX2_M1.Hash181.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JGh_TX2_M1.Hash181.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JGh_TX2_M1.Hash181.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JGh_TX2_M1.Hash181.message=JGh_TX2_M1.Hash181.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JGh_TX2_M1.Hash181.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨152,by omega⟩)=JHe_SHAInputs1.expected ⟨152,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash181.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H152
namespace H153
open JGh_TX2_M1.Hash182
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks15.B012.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks15.B013.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash182.tail).map Fin.val=JGh_TX2_M1.Hash182.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash182.message).map Fin.val=JGh_TX2_M1.Hash182.message := by
  simp only [JGh_TX2_M1.Hash182.message,JGh_TX2_M1.Hash182.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JGh_TX2_M1.Hash182.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JGh_TX2_M1.Hash182.message=JGh_TX2_M1.Hash182.chunks.flatten := by
  have size : JGh_TX2_M1.Hash182.message.length=65 := by
    simp only [JGh_TX2_M1.Hash182.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JGh_TX2_M1.Hash182.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JGh_TX2_M1.Hash182.message,JGh_TX2_M1.Hash182.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JGh_TX2_M1.Hash182.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JGh_TX2_M1.Hash182.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JGh_TX2_M1.Hash182.message=JGh_TX2_M1.Hash182.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JGh_TX2_M1.Hash182.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨153,by omega⟩)=JHe_SHAInputs1.expected ⟨153,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash182.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H153
namespace H154
open JGh_TX2_M1.Hash183
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks15.B014.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks15.B015.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash183.tail).map Fin.val=JGh_TX2_M1.Hash183.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash183.message).map Fin.val=JGh_TX2_M1.Hash183.message := by
  simp only [JGh_TX2_M1.Hash183.message,JGh_TX2_M1.Hash183.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JGh_TX2_M1.Hash183.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JGh_TX2_M1.Hash183.message=JGh_TX2_M1.Hash183.chunks.flatten := by
  have size : JGh_TX2_M1.Hash183.message.length=65 := by
    simp only [JGh_TX2_M1.Hash183.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JGh_TX2_M1.Hash183.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JGh_TX2_M1.Hash183.message,JGh_TX2_M1.Hash183.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JGh_TX2_M1.Hash183.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JGh_TX2_M1.Hash183.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JGh_TX2_M1.Hash183.message=JGh_TX2_M1.Hash183.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JGh_TX2_M1.Hash183.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨154,by omega⟩)=JHe_SHAInputs1.expected ⟨154,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash183.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H154
namespace H155
open JGh_TX2_M1.Hash184
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks15.B016.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks15.B017.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash184.tail).map Fin.val=JGh_TX2_M1.Hash184.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash184.message).map Fin.val=JGh_TX2_M1.Hash184.message := by
  simp only [JGh_TX2_M1.Hash184.message,JGh_TX2_M1.Hash184.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JGh_TX2_M1.Hash184.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JGh_TX2_M1.Hash184.message=JGh_TX2_M1.Hash184.chunks.flatten := by
  have size : JGh_TX2_M1.Hash184.message.length=65 := by
    simp only [JGh_TX2_M1.Hash184.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JGh_TX2_M1.Hash184.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JGh_TX2_M1.Hash184.message,JGh_TX2_M1.Hash184.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JGh_TX2_M1.Hash184.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JGh_TX2_M1.Hash184.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JGh_TX2_M1.Hash184.message=JGh_TX2_M1.Hash184.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JGh_TX2_M1.Hash184.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨155,by omega⟩)=JHe_SHAInputs1.expected ⟨155,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash184.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H155
namespace H156
open JGh_TX2_M1.Hash185
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks15.B018.checked
#print axioms checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks15.B019.checked
#print axioms checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
#print axioms cast00
theorem tailCast : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash185.tail).map Fin.val=JGh_TX2_M1.Hash185.tail := by rfl
#print axioms tailCast
theorem numeric : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash185.message).map Fin.val=JGh_TX2_M1.Hash185.message := by
  simp only [JGh_TX2_M1.Hash185.message,JGh_TX2_M1.Hash185.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
#print axioms numeric
theorem headLengths : ∀ b ∈ JGh_TX2_M1.Hash185.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
#print axioms headLengths
theorem padded : pad JGh_TX2_M1.Hash185.message=JGh_TX2_M1.Hash185.chunks.flatten := by
  have size : JGh_TX2_M1.Hash185.message.length=65 := by
    simp only [JGh_TX2_M1.Hash185.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JGh_TX2_M1.Hash185.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JGh_TX2_M1.Hash185.message,JGh_TX2_M1.Hash185.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JGh_TX2_M1.Hash185.head.flatten) last
#print axioms padded
theorem lengths : ∀ b ∈ JGh_TX2_M1.Hash185.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
#print axioms lengths
theorem hashed : JFp_SHA256.hash JGh_TX2_M1.Hash185.message=JGh_TX2_M1.Hash185.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JGh_TX2_M1.Hash185.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
#print axioms hashed
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨156,by omega⟩)=JHe_SHAInputs1.expected ⟨156,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash185.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H156
end AspisR1.JHx_T1C04
