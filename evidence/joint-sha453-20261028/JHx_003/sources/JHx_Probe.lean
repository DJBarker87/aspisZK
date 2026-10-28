import JHx_Blocks00
import JHe_SHAEquations0
import JGz_HashTools
set_option autoImplicit false
namespace AspisR1.JHx_Probe
open JFp_SHA256
namespace H000
open JHe_C_Gr_M0.Hash000
namespace C00
theorem checked : compress B00.start (words B00.input)=B00.result := JHx_Blocks00.B000.checked
end C00
namespace C01
theorem checked : compress B01.start (words B01.input)=B01.result := JHx_Blocks00.B001.checked
end C01
namespace C02
theorem checked : compress B02.start (words B02.input)=B02.result := JHx_Blocks00.B002.checked
end C02
namespace C03
theorem checked : compress B03.start (words B03.input)=B03.result := JHx_Blocks00.B003.checked
end C03
namespace C04
theorem checked : compress B04.start (words B04.input)=B04.result := JHx_Blocks00.B004.checked
end C04
namespace C05
theorem checked : compress B05.start (words B05.input)=B05.result := JHx_Blocks00.B005.checked
end C05
namespace C06
theorem checked : compress B06.start (words B06.input)=B06.result := JHx_Blocks00.B006.checked
end C06
namespace C07
theorem checked : compress B07.start (words B07.input)=B07.result := JHx_Blocks00.B007.checked
end C07
namespace C08
theorem checked : compress B08.start (words B08.input)=B08.result := JHx_Blocks00.B008.checked
end C08
theorem cast00 : (JGc_TX2_HashBytes.bytes B00.input).map Fin.val=B00.input := by rfl
theorem cast01 : (JGc_TX2_HashBytes.bytes B01.input).map Fin.val=B01.input := by rfl
theorem cast02 : (JGc_TX2_HashBytes.bytes B02.input).map Fin.val=B02.input := by rfl
theorem cast03 : (JGc_TX2_HashBytes.bytes B03.input).map Fin.val=B03.input := by rfl
theorem cast04 : (JGc_TX2_HashBytes.bytes B04.input).map Fin.val=B04.input := by rfl
theorem cast05 : (JGc_TX2_HashBytes.bytes B05.input).map Fin.val=B05.input := by rfl
theorem cast06 : (JGc_TX2_HashBytes.bytes B06.input).map Fin.val=B06.input := by rfl
theorem cast07 : (JGc_TX2_HashBytes.bytes B07.input).map Fin.val=B07.input := by rfl
theorem tailCast : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash000.tail).map Fin.val=JHe_C_Gr_M0.Hash000.tail := by rfl
theorem numeric : (JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash000.message).map Fin.val=JHe_C_Gr_M0.Hash000.message := by
  simp only [JHe_C_Gr_M0.Hash000.message,JHe_C_Gr_M0.Hash000.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast00,cast01,cast02,cast03,cast04,cast05,cast06,cast07,tailCast]
theorem headLengths : ∀ b ∈ JHe_C_Gr_M0.Hash000.head,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input,B02.input,B03.input,B04.input,B05.input,B06.input,B07.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst b; rfl
  · subst b; rfl
  · subst b; rfl
  · subst b; rfl
  · subst b; rfl
  · subst b; rfl
  · subst b; rfl
  · subst b; rfl
theorem padded : pad JHe_C_Gr_M0.Hash000.message=JHe_C_Gr_M0.Hash000.chunks.flatten := by
  have size : JHe_C_Gr_M0.Hash000.message.length=514 := by
    simp only [JHe_C_Gr_M0.Hash000.message,List.length_append]
    rw [JGz_HashTools.length_flatten _ headLengths]
    rfl
  have last : JHe_C_Gr_M0.Hash000.tail ++ [128] ++ List.replicate 53 0 ++ [0,0,0,0,0,0,16,16]=B08.input := by rfl
  unfold pad
  rw [size]
  change JHe_C_Gr_M0.Hash000.head.flatten ++ (JHe_C_Gr_M0.Hash000.tail ++ [128] ++ List.replicate 53 0 ++ [0,0,0,0,0,0,16,16])=JHe_C_Gr_M0.Hash000.head.flatten ++ B08.input
  rw [last]
theorem lengths : ∀ b ∈ JHe_C_Gr_M0.Hash000.chunks,b.length=64 := by
  intro b hb
  change b ∈ [B00.input,B01.input,B02.input,B03.input,B04.input,B05.input,B06.input,B07.input,B08.input] at hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · subst b; rfl
  · subst b; rfl
  · subst b; rfl
  · subst b; rfl
  · subst b; rfl
  · subst b; rfl
  · subst b; rfl
  · subst b; rfl
  · subst b; rfl
theorem hashed : JFp_SHA256.hash JHe_C_Gr_M0.Hash000.message=JHe_C_Gr_M0.Hash000.result := by
  rw [JGz_HashTools.hash_chunks _ _ padded lengths]
  change [B00.input,B01.input,B02.input,B03.input,B04.input,B05.input,B06.input,B07.input,B08.input].foldl (fun s b=>compress s (words b)) initial=JHe_C_Gr_M0.Hash000.result
  rw [List.foldl_cons,show initial=B00.start from rfl,C00.checked]
  rw [List.foldl_cons,show B00.result=B01.start from rfl,C01.checked]
  rw [List.foldl_cons,show B01.result=B02.start from rfl,C02.checked]
  rw [List.foldl_cons,show B02.result=B03.start from rfl,C03.checked]
  rw [List.foldl_cons,show B03.result=B04.start from rfl,C04.checked]
  rw [List.foldl_cons,show B04.result=B05.start from rfl,C05.checked]
  rw [List.foldl_cons,show B05.result=B06.start from rfl,C06.checked]
  rw [List.foldl_cons,show B06.result=B07.start from rfl,C07.checked]
  rw [List.foldl_cons,show B07.result=B08.start from rfl,C08.checked]
  rfl
theorem source : JFp_SHADigest.digest (JHe_SHAInputs0.input ⟨0,by omega⟩)=JHe_SHAInputs0.expected ⟨0,by omega⟩ := by
  change JFp_SHADigest.output (JFp_SHA256.hash ((JGc_TX2_HashBytes.bytes JHe_C_Gr_M0.Hash000.message).map Fin.val))=_
  rw [numeric,hashed]
  funext i
  fin_cases i <;> rfl
#print axioms source
end H000
end AspisR1.JHx_Probe
