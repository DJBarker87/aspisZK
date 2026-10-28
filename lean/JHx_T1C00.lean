import JHx_Blocks14
import JHx_Blocks15
import JHx_Blocks16
import JHe_SHAEquations1
import JGz_HashTools
set_option autoImplicit false
namespace AspisR1.JHx_T1C00
open JFp_SHA256
namespace H000
open JHe_C_Gr_M1.Hash000
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks14.B004.checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks14.B005.checked
end C01
namespace C02
theorem checked : compress B02.start (words B02.input)=B02.result := JHx_Blocks14.B006.checked
end C02
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
theorem cast01 : (JGc_TX2_HashBytes.bytes B01.input).map Fin.val=B01.input := by rfl
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash000.tail).map Fin.val=JHe_C_Gr_M1.Hash000.tail := by rfl
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash000.message).map Fin.val=JHe_C_Gr_M1.Hash000.message := by
  simp only [JHe_C_Gr_M1.Hash000.message,JHe_C_Gr_M1.Hash000.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,cast01,tailCast]
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash000.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
theorem padded : pad JHe_C_Gr_M1.Hash000.message=JHe_C_Gr_M1.Hash000.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash000.message.length=162 := by
    simp only [JHe_C_Gr_M1.Hash000.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash000.tail ++ [128] ++ List.replicate 21 0 ++ [0,0,0,0,0,0,5,16]=B02.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash000.message,JHe_C_Gr_M1.Hash000.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash000.head.flatten) last
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash000.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input,B02.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1 | h2
  · subst b; rfl
  · subst b; rfl
  · subst b; rfl
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash000.message=JHe_C_Gr_M1.Hash000.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input,B02.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash000.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rw [List.foldl_cons,show B01.result=B02.start from rfl,C02.checked]
  rfl
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨0,by omega⟩)=JHe_SHAInputs1.expected ⟨0,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash000.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H000
namespace H001
open JHe_C_Gr_M1.Hash001
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks14.B007.checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks14.B008.checked
end C01
namespace C02
theorem checked : compress B02.start (words B02.input)=B02.result := JHx_Blocks14.B009.checked
end C02
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
theorem cast01 : (JGc_TX2_HashBytes.bytes B01.input).map Fin.val=B01.input := by rfl
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash001.tail).map Fin.val=JHe_C_Gr_M1.Hash001.tail := by rfl
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash001.message).map Fin.val=JHe_C_Gr_M1.Hash001.message := by
  simp only [JHe_C_Gr_M1.Hash001.message,JHe_C_Gr_M1.Hash001.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,cast01,tailCast]
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash001.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
theorem padded : pad JHe_C_Gr_M1.Hash001.message=JHe_C_Gr_M1.Hash001.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash001.message.length=162 := by
    simp only [JHe_C_Gr_M1.Hash001.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash001.tail ++ [128] ++ List.replicate 21 0 ++ [0,0,0,0,0,0,5,16]=B02.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash001.message,JHe_C_Gr_M1.Hash001.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash001.head.flatten) last
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash001.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input,B02.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1 | h2
  · subst b; rfl
  · subst b; rfl
  · subst b; rfl
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash001.message=JHe_C_Gr_M1.Hash001.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input,B02.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash001.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rw [List.foldl_cons,show B01.result=B02.start from rfl,C02.checked]
  rfl
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨1,by omega⟩)=JHe_SHAInputs1.expected ⟨1,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash001.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H001
namespace H002
open JHe_C_Gr_M1.Hash002
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks14.B010.checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks14.B011.checked
end C01
namespace C02
theorem checked : compress B02.start (words B02.input)=B02.result := JHx_Blocks14.B012.checked
end C02
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
theorem cast01 : (JGc_TX2_HashBytes.bytes B01.input).map Fin.val=B01.input := by rfl
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash002.tail).map Fin.val=JHe_C_Gr_M1.Hash002.tail := by rfl
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash002.message).map Fin.val=JHe_C_Gr_M1.Hash002.message := by
  simp only [JHe_C_Gr_M1.Hash002.message,JHe_C_Gr_M1.Hash002.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,cast01,tailCast]
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash002.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
theorem padded : pad JHe_C_Gr_M1.Hash002.message=JHe_C_Gr_M1.Hash002.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash002.message.length=162 := by
    simp only [JHe_C_Gr_M1.Hash002.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash002.tail ++ [128] ++ List.replicate 21 0 ++ [0,0,0,0,0,0,5,16]=B02.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash002.message,JHe_C_Gr_M1.Hash002.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash002.head.flatten) last
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash002.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input,B02.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1 | h2
  · subst b; rfl
  · subst b; rfl
  · subst b; rfl
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash002.message=JHe_C_Gr_M1.Hash002.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input,B02.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash002.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rw [List.foldl_cons,show B01.result=B02.start from rfl,C02.checked]
  rfl
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨2,by omega⟩)=JHe_SHAInputs1.expected ⟨2,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash002.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H002
namespace H003
open JHe_C_Gr_M1.Hash003
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks14.B013.checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks14.B014.checked
end C01
namespace C02
theorem checked : compress B02.start (words B02.input)=B02.result := JHx_Blocks14.B015.checked
end C02
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
theorem cast01 : (JGc_TX2_HashBytes.bytes B01.input).map Fin.val=B01.input := by rfl
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash003.tail).map Fin.val=JHe_C_Gr_M1.Hash003.tail := by rfl
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash003.message).map Fin.val=JHe_C_Gr_M1.Hash003.message := by
  simp only [JHe_C_Gr_M1.Hash003.message,JHe_C_Gr_M1.Hash003.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,cast01,tailCast]
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash003.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
theorem padded : pad JHe_C_Gr_M1.Hash003.message=JHe_C_Gr_M1.Hash003.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash003.message.length=162 := by
    simp only [JHe_C_Gr_M1.Hash003.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash003.tail ++ [128] ++ List.replicate 21 0 ++ [0,0,0,0,0,0,5,16]=B02.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash003.message,JHe_C_Gr_M1.Hash003.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash003.head.flatten) last
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash003.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input,B02.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1 | h2
  · subst b; rfl
  · subst b; rfl
  · subst b; rfl
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash003.message=JHe_C_Gr_M1.Hash003.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input,B02.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash003.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rw [List.foldl_cons,show B01.result=B02.start from rfl,C02.checked]
  rfl
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨3,by omega⟩)=JHe_SHAInputs1.expected ⟨3,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash003.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H003
namespace H004
open JHe_C_Gr_M1.Hash004
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks14.B016.checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks14.B017.checked
end C01
namespace C02
theorem checked : compress B02.start (words B02.input)=B02.result := JHx_Blocks14.B018.checked
end C02
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
theorem cast01 : (JGc_TX2_HashBytes.bytes B01.input).map Fin.val=B01.input := by rfl
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash004.tail).map Fin.val=JHe_C_Gr_M1.Hash004.tail := by rfl
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash004.message).map Fin.val=JHe_C_Gr_M1.Hash004.message := by
  simp only [JHe_C_Gr_M1.Hash004.message,JHe_C_Gr_M1.Hash004.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,cast01,tailCast]
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash004.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
theorem padded : pad JHe_C_Gr_M1.Hash004.message=JHe_C_Gr_M1.Hash004.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash004.message.length=162 := by
    simp only [JHe_C_Gr_M1.Hash004.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash004.tail ++ [128] ++ List.replicate 21 0 ++ [0,0,0,0,0,0,5,16]=B02.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash004.message,JHe_C_Gr_M1.Hash004.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash004.head.flatten) last
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash004.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input,B02.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1 | h2
  · subst b; rfl
  · subst b; rfl
  · subst b; rfl
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash004.message=JHe_C_Gr_M1.Hash004.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input,B02.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash004.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rw [List.foldl_cons,show B01.result=B02.start from rfl,C02.checked]
  rfl
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨4,by omega⟩)=JHe_SHAInputs1.expected ⟨4,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash004.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H004
namespace H005
open JHe_C_Gr_M1.Hash005
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks14.B019.checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks14.B020.checked
end C01
namespace C02
theorem checked : compress B02.start (words B02.input)=B02.result := JHx_Blocks14.B021.checked
end C02
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
theorem cast01 : (JGc_TX2_HashBytes.bytes B01.input).map Fin.val=B01.input := by rfl
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash005.tail).map Fin.val=JHe_C_Gr_M1.Hash005.tail := by rfl
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash005.message).map Fin.val=JHe_C_Gr_M1.Hash005.message := by
  simp only [JHe_C_Gr_M1.Hash005.message,JHe_C_Gr_M1.Hash005.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,cast01,tailCast]
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash005.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
theorem padded : pad JHe_C_Gr_M1.Hash005.message=JHe_C_Gr_M1.Hash005.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash005.message.length=162 := by
    simp only [JHe_C_Gr_M1.Hash005.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash005.tail ++ [128] ++ List.replicate 21 0 ++ [0,0,0,0,0,0,5,16]=B02.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash005.message,JHe_C_Gr_M1.Hash005.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash005.head.flatten) last
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash005.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input,B02.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1 | h2
  · subst b; rfl
  · subst b; rfl
  · subst b; rfl
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash005.message=JHe_C_Gr_M1.Hash005.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input,B02.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash005.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rw [List.foldl_cons,show B01.result=B02.start from rfl,C02.checked]
  rfl
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨5,by omega⟩)=JHe_SHAInputs1.expected ⟨5,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash005.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H005
namespace H006
open JHe_C_Gr_M1.Hash006
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks14.B022.checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks14.B023.checked
end C01
namespace C02
theorem checked : compress B02.start (words B02.input)=B02.result := JHx_Blocks14.B024.checked
end C02
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
theorem cast01 : (JGc_TX2_HashBytes.bytes B01.input).map Fin.val=B01.input := by rfl
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash006.tail).map Fin.val=JHe_C_Gr_M1.Hash006.tail := by rfl
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash006.message).map Fin.val=JHe_C_Gr_M1.Hash006.message := by
  simp only [JHe_C_Gr_M1.Hash006.message,JHe_C_Gr_M1.Hash006.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,cast01,tailCast]
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash006.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
theorem padded : pad JHe_C_Gr_M1.Hash006.message=JHe_C_Gr_M1.Hash006.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash006.message.length=162 := by
    simp only [JHe_C_Gr_M1.Hash006.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash006.tail ++ [128] ++ List.replicate 21 0 ++ [0,0,0,0,0,0,5,16]=B02.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash006.message,JHe_C_Gr_M1.Hash006.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash006.head.flatten) last
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash006.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input,B02.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1 | h2
  · subst b; rfl
  · subst b; rfl
  · subst b; rfl
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash006.message=JHe_C_Gr_M1.Hash006.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input,B02.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash006.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rw [List.foldl_cons,show B01.result=B02.start from rfl,C02.checked]
  rfl
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨6,by omega⟩)=JHe_SHAInputs1.expected ⟨6,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash006.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H006
namespace H007
open JHe_C_Gr_M1.Hash007
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks14.B025.checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks14.B026.checked
end C01
namespace C02
theorem checked : compress B02.start (words B02.input)=B02.result := JHx_Blocks14.B027.checked
end C02
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
theorem cast01 : (JGc_TX2_HashBytes.bytes B01.input).map Fin.val=B01.input := by rfl
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash007.tail).map Fin.val=JHe_C_Gr_M1.Hash007.tail := by rfl
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash007.message).map Fin.val=JHe_C_Gr_M1.Hash007.message := by
  simp only [JHe_C_Gr_M1.Hash007.message,JHe_C_Gr_M1.Hash007.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,cast01,tailCast]
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash007.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
theorem padded : pad JHe_C_Gr_M1.Hash007.message=JHe_C_Gr_M1.Hash007.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash007.message.length=162 := by
    simp only [JHe_C_Gr_M1.Hash007.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash007.tail ++ [128] ++ List.replicate 21 0 ++ [0,0,0,0,0,0,5,16]=B02.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash007.message,JHe_C_Gr_M1.Hash007.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash007.head.flatten) last
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash007.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input,B02.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1 | h2
  · subst b; rfl
  · subst b; rfl
  · subst b; rfl
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash007.message=JHe_C_Gr_M1.Hash007.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input,B02.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash007.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rw [List.foldl_cons,show B01.result=B02.start from rfl,C02.checked]
  rfl
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨7,by omega⟩)=JHe_SHAInputs1.expected ⟨7,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash007.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H007
namespace H008
open JHe_C_Gr_M1.Hash008
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks15.B000.checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks15.B001.checked
end C01
namespace C02
theorem checked : compress B02.start (words B02.input)=B02.result := JHx_Blocks15.B002.checked
end C02
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
theorem cast01 : (JGc_TX2_HashBytes.bytes B01.input).map Fin.val=B01.input := by rfl
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash008.tail).map Fin.val=JHe_C_Gr_M1.Hash008.tail := by rfl
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash008.message).map Fin.val=JHe_C_Gr_M1.Hash008.message := by
  simp only [JHe_C_Gr_M1.Hash008.message,JHe_C_Gr_M1.Hash008.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,cast01,tailCast]
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash008.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
theorem padded : pad JHe_C_Gr_M1.Hash008.message=JHe_C_Gr_M1.Hash008.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash008.message.length=162 := by
    simp only [JHe_C_Gr_M1.Hash008.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash008.tail ++ [128] ++ List.replicate 21 0 ++ [0,0,0,0,0,0,5,16]=B02.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash008.message,JHe_C_Gr_M1.Hash008.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash008.head.flatten) last
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash008.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input,B02.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1 | h2
  · subst b; rfl
  · subst b; rfl
  · subst b; rfl
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash008.message=JHe_C_Gr_M1.Hash008.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input,B02.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash008.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rw [List.foldl_cons,show B01.result=B02.start from rfl,C02.checked]
  rfl
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨8,by omega⟩)=JHe_SHAInputs1.expected ⟨8,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash008.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H008
namespace H009
open JHe_C_Gr_M1.Hash009
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks15.B003.checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks15.B004.checked
end C01
namespace C02
theorem checked : compress B02.start (words B02.input)=B02.result := JHx_Blocks15.B005.checked
end C02
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
theorem cast01 : (JGc_TX2_HashBytes.bytes B01.input).map Fin.val=B01.input := by rfl
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash009.tail).map Fin.val=JHe_C_Gr_M1.Hash009.tail := by rfl
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash009.message).map Fin.val=JHe_C_Gr_M1.Hash009.message := by
  simp only [JHe_C_Gr_M1.Hash009.message,JHe_C_Gr_M1.Hash009.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,cast01,tailCast]
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash009.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
theorem padded : pad JHe_C_Gr_M1.Hash009.message=JHe_C_Gr_M1.Hash009.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash009.message.length=162 := by
    simp only [JHe_C_Gr_M1.Hash009.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash009.tail ++ [128] ++ List.replicate 21 0 ++ [0,0,0,0,0,0,5,16]=B02.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash009.message,JHe_C_Gr_M1.Hash009.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash009.head.flatten) last
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash009.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input,B02.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1 | h2
  · subst b; rfl
  · subst b; rfl
  · subst b; rfl
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash009.message=JHe_C_Gr_M1.Hash009.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input,B02.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash009.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rw [List.foldl_cons,show B01.result=B02.start from rfl,C02.checked]
  rfl
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨9,by omega⟩)=JHe_SHAInputs1.expected ⟨9,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash009.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H009
namespace H010
open JHe_C_Gr_M1.Hash010
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks15.B006.checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks15.B007.checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash010.tail).map Fin.val=JHe_C_Gr_M1.Hash010.tail := by rfl
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash010.message).map Fin.val=JHe_C_Gr_M1.Hash010.message := by
  simp only [JHe_C_Gr_M1.Hash010.message,JHe_C_Gr_M1.Hash010.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash010.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
theorem padded : pad JHe_C_Gr_M1.Hash010.message=JHe_C_Gr_M1.Hash010.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash010.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash010.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash010.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash010.message,JHe_C_Gr_M1.Hash010.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash010.head.flatten) last
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash010.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash010.message=JHe_C_Gr_M1.Hash010.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash010.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨10,by omega⟩)=JHe_SHAInputs1.expected ⟨10,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash010.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H010
namespace H011
open JHe_C_Gr_M1.Hash011
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks15.B008.checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks15.B009.checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash011.tail).map Fin.val=JHe_C_Gr_M1.Hash011.tail := by rfl
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash011.message).map Fin.val=JHe_C_Gr_M1.Hash011.message := by
  simp only [JHe_C_Gr_M1.Hash011.message,JHe_C_Gr_M1.Hash011.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash011.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
theorem padded : pad JHe_C_Gr_M1.Hash011.message=JHe_C_Gr_M1.Hash011.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash011.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash011.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash011.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash011.message,JHe_C_Gr_M1.Hash011.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash011.head.flatten) last
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash011.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash011.message=JHe_C_Gr_M1.Hash011.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash011.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨11,by omega⟩)=JHe_SHAInputs1.expected ⟨11,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash011.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H011
namespace H012
open JHe_C_Gr_M1.Hash012
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks15.B010.checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks15.B011.checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash012.tail).map Fin.val=JHe_C_Gr_M1.Hash012.tail := by rfl
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash012.message).map Fin.val=JHe_C_Gr_M1.Hash012.message := by
  simp only [JHe_C_Gr_M1.Hash012.message,JHe_C_Gr_M1.Hash012.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash012.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
theorem padded : pad JHe_C_Gr_M1.Hash012.message=JHe_C_Gr_M1.Hash012.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash012.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash012.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash012.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash012.message,JHe_C_Gr_M1.Hash012.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash012.head.flatten) last
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash012.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash012.message=JHe_C_Gr_M1.Hash012.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash012.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨12,by omega⟩)=JHe_SHAInputs1.expected ⟨12,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash012.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H012
namespace H013
open JHe_C_Gr_M1.Hash013
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks15.B012.checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks15.B013.checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash013.tail).map Fin.val=JHe_C_Gr_M1.Hash013.tail := by rfl
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash013.message).map Fin.val=JHe_C_Gr_M1.Hash013.message := by
  simp only [JHe_C_Gr_M1.Hash013.message,JHe_C_Gr_M1.Hash013.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash013.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
theorem padded : pad JHe_C_Gr_M1.Hash013.message=JHe_C_Gr_M1.Hash013.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash013.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash013.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash013.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash013.message,JHe_C_Gr_M1.Hash013.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash013.head.flatten) last
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash013.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash013.message=JHe_C_Gr_M1.Hash013.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash013.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨13,by omega⟩)=JHe_SHAInputs1.expected ⟨13,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash013.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H013
namespace H014
open JHe_C_Gr_M1.Hash014
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks15.B014.checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks15.B015.checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash014.tail).map Fin.val=JHe_C_Gr_M1.Hash014.tail := by rfl
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash014.message).map Fin.val=JHe_C_Gr_M1.Hash014.message := by
  simp only [JHe_C_Gr_M1.Hash014.message,JHe_C_Gr_M1.Hash014.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash014.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
theorem padded : pad JHe_C_Gr_M1.Hash014.message=JHe_C_Gr_M1.Hash014.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash014.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash014.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash014.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash014.message,JHe_C_Gr_M1.Hash014.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash014.head.flatten) last
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash014.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash014.message=JHe_C_Gr_M1.Hash014.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash014.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨14,by omega⟩)=JHe_SHAInputs1.expected ⟨14,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash014.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H014
namespace H015
open JHe_C_Gr_M1.Hash015
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks15.B016.checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks15.B017.checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash015.tail).map Fin.val=JHe_C_Gr_M1.Hash015.tail := by rfl
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash015.message).map Fin.val=JHe_C_Gr_M1.Hash015.message := by
  simp only [JHe_C_Gr_M1.Hash015.message,JHe_C_Gr_M1.Hash015.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash015.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
theorem padded : pad JHe_C_Gr_M1.Hash015.message=JHe_C_Gr_M1.Hash015.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash015.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash015.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash015.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash015.message,JHe_C_Gr_M1.Hash015.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash015.head.flatten) last
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash015.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash015.message=JHe_C_Gr_M1.Hash015.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash015.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨15,by omega⟩)=JHe_SHAInputs1.expected ⟨15,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash015.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H015
namespace H016
open JHe_C_Gr_M1.Hash016
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks15.B018.checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks15.B019.checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash016.tail).map Fin.val=JHe_C_Gr_M1.Hash016.tail := by rfl
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash016.message).map Fin.val=JHe_C_Gr_M1.Hash016.message := by
  simp only [JHe_C_Gr_M1.Hash016.message,JHe_C_Gr_M1.Hash016.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash016.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
theorem padded : pad JHe_C_Gr_M1.Hash016.message=JHe_C_Gr_M1.Hash016.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash016.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash016.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash016.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash016.message,JHe_C_Gr_M1.Hash016.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash016.head.flatten) last
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash016.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash016.message=JHe_C_Gr_M1.Hash016.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash016.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨16,by omega⟩)=JHe_SHAInputs1.expected ⟨16,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash016.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H016
namespace H017
open JHe_C_Gr_M1.Hash017
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks15.B020.checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks15.B021.checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash017.tail).map Fin.val=JHe_C_Gr_M1.Hash017.tail := by rfl
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash017.message).map Fin.val=JHe_C_Gr_M1.Hash017.message := by
  simp only [JHe_C_Gr_M1.Hash017.message,JHe_C_Gr_M1.Hash017.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash017.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
theorem padded : pad JHe_C_Gr_M1.Hash017.message=JHe_C_Gr_M1.Hash017.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash017.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash017.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash017.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash017.message,JHe_C_Gr_M1.Hash017.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash017.head.flatten) last
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash017.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash017.message=JHe_C_Gr_M1.Hash017.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash017.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨17,by omega⟩)=JHe_SHAInputs1.expected ⟨17,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash017.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H017
namespace H018
open JHe_C_Gr_M1.Hash018
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks15.B022.checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks15.B023.checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash018.tail).map Fin.val=JHe_C_Gr_M1.Hash018.tail := by rfl
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash018.message).map Fin.val=JHe_C_Gr_M1.Hash018.message := by
  simp only [JHe_C_Gr_M1.Hash018.message,JHe_C_Gr_M1.Hash018.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash018.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
theorem padded : pad JHe_C_Gr_M1.Hash018.message=JHe_C_Gr_M1.Hash018.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash018.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash018.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash018.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash018.message,JHe_C_Gr_M1.Hash018.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash018.head.flatten) last
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash018.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash018.message=JHe_C_Gr_M1.Hash018.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash018.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨18,by omega⟩)=JHe_SHAInputs1.expected ⟨18,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash018.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H018
namespace H019
open JHe_C_Gr_M1.Hash019
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks15.B024.checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks15.B025.checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash019.tail).map Fin.val=JHe_C_Gr_M1.Hash019.tail := by rfl
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash019.message).map Fin.val=JHe_C_Gr_M1.Hash019.message := by
  simp only [JHe_C_Gr_M1.Hash019.message,JHe_C_Gr_M1.Hash019.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash019.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
theorem padded : pad JHe_C_Gr_M1.Hash019.message=JHe_C_Gr_M1.Hash019.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash019.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash019.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash019.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash019.message,JHe_C_Gr_M1.Hash019.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash019.head.flatten) last
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash019.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash019.message=JHe_C_Gr_M1.Hash019.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash019.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨19,by omega⟩)=JHe_SHAInputs1.expected ⟨19,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash019.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H019
namespace H020
open JHe_C_Gr_M1.Hash020
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks15.B026.checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks15.B027.checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash020.tail).map Fin.val=JHe_C_Gr_M1.Hash020.tail := by rfl
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash020.message).map Fin.val=JHe_C_Gr_M1.Hash020.message := by
  simp only [JHe_C_Gr_M1.Hash020.message,JHe_C_Gr_M1.Hash020.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash020.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
theorem padded : pad JHe_C_Gr_M1.Hash020.message=JHe_C_Gr_M1.Hash020.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash020.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash020.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash020.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash020.message,JHe_C_Gr_M1.Hash020.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash020.head.flatten) last
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash020.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash020.message=JHe_C_Gr_M1.Hash020.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash020.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨20,by omega⟩)=JHe_SHAInputs1.expected ⟨20,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash020.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H020
namespace H021
open JHe_C_Gr_M1.Hash021
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks16.B000.checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks16.B001.checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash021.tail).map Fin.val=JHe_C_Gr_M1.Hash021.tail := by rfl
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash021.message).map Fin.val=JHe_C_Gr_M1.Hash021.message := by
  simp only [JHe_C_Gr_M1.Hash021.message,JHe_C_Gr_M1.Hash021.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash021.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
theorem padded : pad JHe_C_Gr_M1.Hash021.message=JHe_C_Gr_M1.Hash021.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash021.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash021.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash021.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash021.message,JHe_C_Gr_M1.Hash021.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash021.head.flatten) last
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash021.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash021.message=JHe_C_Gr_M1.Hash021.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash021.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨21,by omega⟩)=JHe_SHAInputs1.expected ⟨21,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash021.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H021
namespace H022
open JHe_C_Gr_M1.Hash022
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks16.B002.checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks16.B003.checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash022.tail).map Fin.val=JHe_C_Gr_M1.Hash022.tail := by rfl
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash022.message).map Fin.val=JHe_C_Gr_M1.Hash022.message := by
  simp only [JHe_C_Gr_M1.Hash022.message,JHe_C_Gr_M1.Hash022.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash022.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
theorem padded : pad JHe_C_Gr_M1.Hash022.message=JHe_C_Gr_M1.Hash022.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash022.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash022.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash022.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash022.message,JHe_C_Gr_M1.Hash022.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash022.head.flatten) last
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash022.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash022.message=JHe_C_Gr_M1.Hash022.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash022.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨22,by omega⟩)=JHe_SHAInputs1.expected ⟨22,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash022.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H022
namespace H023
open JHe_C_Gr_M1.Hash023
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks16.B004.checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks16.B005.checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash023.tail).map Fin.val=JHe_C_Gr_M1.Hash023.tail := by rfl
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash023.message).map Fin.val=JHe_C_Gr_M1.Hash023.message := by
  simp only [JHe_C_Gr_M1.Hash023.message,JHe_C_Gr_M1.Hash023.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash023.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
theorem padded : pad JHe_C_Gr_M1.Hash023.message=JHe_C_Gr_M1.Hash023.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash023.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash023.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash023.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash023.message,JHe_C_Gr_M1.Hash023.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash023.head.flatten) last
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash023.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash023.message=JHe_C_Gr_M1.Hash023.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash023.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨23,by omega⟩)=JHe_SHAInputs1.expected ⟨23,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash023.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H023
namespace H024
open JHe_C_Gr_M1.Hash024
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks16.B006.checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks16.B007.checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash024.tail).map Fin.val=JHe_C_Gr_M1.Hash024.tail := by rfl
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash024.message).map Fin.val=JHe_C_Gr_M1.Hash024.message := by
  simp only [JHe_C_Gr_M1.Hash024.message,JHe_C_Gr_M1.Hash024.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash024.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
theorem padded : pad JHe_C_Gr_M1.Hash024.message=JHe_C_Gr_M1.Hash024.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash024.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash024.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash024.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash024.message,JHe_C_Gr_M1.Hash024.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash024.head.flatten) last
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash024.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash024.message=JHe_C_Gr_M1.Hash024.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash024.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨24,by omega⟩)=JHe_SHAInputs1.expected ⟨24,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash024.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H024
namespace H025
open JHe_C_Gr_M1.Hash025
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks16.B008.checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks16.B009.checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash025.tail).map Fin.val=JHe_C_Gr_M1.Hash025.tail := by rfl
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash025.message).map Fin.val=JHe_C_Gr_M1.Hash025.message := by
  simp only [JHe_C_Gr_M1.Hash025.message,JHe_C_Gr_M1.Hash025.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash025.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
theorem padded : pad JHe_C_Gr_M1.Hash025.message=JHe_C_Gr_M1.Hash025.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash025.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash025.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash025.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash025.message,JHe_C_Gr_M1.Hash025.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash025.head.flatten) last
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash025.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash025.message=JHe_C_Gr_M1.Hash025.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash025.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨25,by omega⟩)=JHe_SHAInputs1.expected ⟨25,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash025.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H025
namespace H026
open JHe_C_Gr_M1.Hash026
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks16.B010.checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks16.B011.checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash026.tail).map Fin.val=JHe_C_Gr_M1.Hash026.tail := by rfl
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash026.message).map Fin.val=JHe_C_Gr_M1.Hash026.message := by
  simp only [JHe_C_Gr_M1.Hash026.message,JHe_C_Gr_M1.Hash026.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash026.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
theorem padded : pad JHe_C_Gr_M1.Hash026.message=JHe_C_Gr_M1.Hash026.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash026.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash026.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash026.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash026.message,JHe_C_Gr_M1.Hash026.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash026.head.flatten) last
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash026.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash026.message=JHe_C_Gr_M1.Hash026.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash026.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨26,by omega⟩)=JHe_SHAInputs1.expected ⟨26,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash026.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H026
namespace H027
open JHe_C_Gr_M1.Hash027
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks16.B012.checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks16.B013.checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash027.tail).map Fin.val=JHe_C_Gr_M1.Hash027.tail := by rfl
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash027.message).map Fin.val=JHe_C_Gr_M1.Hash027.message := by
  simp only [JHe_C_Gr_M1.Hash027.message,JHe_C_Gr_M1.Hash027.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash027.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
theorem padded : pad JHe_C_Gr_M1.Hash027.message=JHe_C_Gr_M1.Hash027.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash027.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash027.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash027.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash027.message,JHe_C_Gr_M1.Hash027.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash027.head.flatten) last
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash027.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash027.message=JHe_C_Gr_M1.Hash027.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash027.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨27,by omega⟩)=JHe_SHAInputs1.expected ⟨27,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash027.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H027
namespace H028
open JHe_C_Gr_M1.Hash028
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks16.B014.checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks16.B015.checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash028.tail).map Fin.val=JHe_C_Gr_M1.Hash028.tail := by rfl
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash028.message).map Fin.val=JHe_C_Gr_M1.Hash028.message := by
  simp only [JHe_C_Gr_M1.Hash028.message,JHe_C_Gr_M1.Hash028.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash028.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
theorem padded : pad JHe_C_Gr_M1.Hash028.message=JHe_C_Gr_M1.Hash028.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash028.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash028.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash028.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash028.message,JHe_C_Gr_M1.Hash028.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash028.head.flatten) last
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash028.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash028.message=JHe_C_Gr_M1.Hash028.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash028.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨28,by omega⟩)=JHe_SHAInputs1.expected ⟨28,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash028.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H028
namespace H029
open JHe_C_Gr_M1.Hash029
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks16.B016.checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks16.B017.checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash029.tail).map Fin.val=JHe_C_Gr_M1.Hash029.tail := by rfl
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash029.message).map Fin.val=JHe_C_Gr_M1.Hash029.message := by
  simp only [JHe_C_Gr_M1.Hash029.message,JHe_C_Gr_M1.Hash029.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash029.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
theorem padded : pad JHe_C_Gr_M1.Hash029.message=JHe_C_Gr_M1.Hash029.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash029.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash029.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash029.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash029.message,JHe_C_Gr_M1.Hash029.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash029.head.flatten) last
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash029.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash029.message=JHe_C_Gr_M1.Hash029.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash029.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨29,by omega⟩)=JHe_SHAInputs1.expected ⟨29,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash029.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H029
namespace H030
open JHe_C_Gr_M1.Hash030
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks16.B018.checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks16.B019.checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash030.tail).map Fin.val=JHe_C_Gr_M1.Hash030.tail := by rfl
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash030.message).map Fin.val=JHe_C_Gr_M1.Hash030.message := by
  simp only [JHe_C_Gr_M1.Hash030.message,JHe_C_Gr_M1.Hash030.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash030.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
theorem padded : pad JHe_C_Gr_M1.Hash030.message=JHe_C_Gr_M1.Hash030.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash030.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash030.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash030.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash030.message,JHe_C_Gr_M1.Hash030.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash030.head.flatten) last
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash030.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash030.message=JHe_C_Gr_M1.Hash030.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash030.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨30,by omega⟩)=JHe_SHAInputs1.expected ⟨30,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash030.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H030
namespace H031
open JHe_C_Gr_M1.Hash031
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks16.B020.checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks16.B021.checked
end C01
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash031.tail).map Fin.val=JHe_C_Gr_M1.Hash031.tail := by rfl
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash031.message).map Fin.val=JHe_C_Gr_M1.Hash031.message := by
  simp only [JHe_C_Gr_M1.Hash031.message,JHe_C_Gr_M1.Hash031.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,tailCast]
theorem headLengths : ∀ b ∈ JHe_C_Gr_M1.Hash031.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0
  · subst b; rfl
theorem padded : pad JHe_C_Gr_M1.Hash031.message=JHe_C_Gr_M1.Hash031.chunks.flatten := by
  have size : JHe_C_Gr_M1.Hash031.message.length=65 := by
    simp only [JHe_C_Gr_M1.Hash031.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M1.Hash031.tail ++ [128] ++ List.replicate 54 0 ++ [0,0,0,0,0,0,2,8]=B01.input := by rfl
  unfold pad
  rw [size]
  rw [JHe_C_Gr_M1.Hash031.message,JHe_C_Gr_M1.Hash031.chunks]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
  simp only [List.append_assoc] at last ⊢
  exact congrArg (List.append JHe_C_Gr_M1.Hash031.head.flatten) last
theorem lengths : ∀ b ∈ JHe_C_Gr_M1.Hash031.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1
  · subst b; rfl
  · subst b; rfl
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M1.Hash031.message=JHe_C_Gr_M1.Hash031.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M1.Hash031.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rfl
theorem source : JFp_SHADigest.digest (JHe_SHAInputs1.input ⟨31,by omega⟩)=JHe_SHAInputs1.expected ⟨31,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M1.Hash031.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H031
end AspisR1.JHx_T1C00
