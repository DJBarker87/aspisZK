import NDO_JGz_SHAC00
set_option autoImplicit false
namespace AspisR1.JGz_SHAC0Fold
open JFp_SHA256
open JGz_SHAC00
theorem folded : chunks.foldl (fun s b=>compress s (words b)) B000.start=B015.result := by
  unfold chunks
  simp only [List.foldl_cons,List.foldl_nil]
  rw [B000.checked]
  rw [show B000.result=B001.start from rfl]
  rw [B001.checked]
  rw [show B001.result=B002.start from rfl]
  rw [B002.checked]
  rw [show B002.result=B003.start from rfl]
  rw [B003.checked]
  rw [show B003.result=B004.start from rfl]
  rw [B004.checked]
  rw [show B004.result=B005.start from rfl]
  rw [B005.checked]
  rw [show B005.result=B006.start from rfl]
  rw [B006.checked]
  rw [show B006.result=B007.start from rfl]
  rw [B007.checked]
  rw [show B007.result=B008.start from rfl]
  rw [B008.checked]
  rw [show B008.result=B009.start from rfl]
  rw [B009.checked]
  rw [show B009.result=B010.start from rfl]
  rw [B010.checked]
  rw [show B010.result=B011.start from rfl]
  rw [B011.checked]
  rw [show B011.result=B012.start from rfl]
  rw [B012.checked]
  rw [show B012.result=B013.start from rfl]
  rw [B013.checked]
  rw [show B013.result=B014.start from rfl]
  rw [B014.checked]
  rw [show B014.result=B015.start from rfl]
  rw [B015.checked]
#print axioms folded
theorem lengths : ∀ b ∈ chunks,b.length=64 := by
  intro b hb
  simp only [chunks,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15
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
  · subst b;rfl
  · subst b;rfl
  · subst b;rfl
#print axioms lengths
end AspisR1.JGz_SHAC0Fold
