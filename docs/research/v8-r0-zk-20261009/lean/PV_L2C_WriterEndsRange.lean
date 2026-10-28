import PV_L2C_BlockRange
set_option autoImplicit false
namespace PV_L2C_WriterEndsRange
open Aeneas Aeneas.Std Result R0Z.WriterRefine PV_L2C_BlockRange

theorem init (domain len : U32) (hd : domain.val < 2147483647)
    (hl : len.val < 2147483647) (s : Array U32 16#usize)
    (hs : R0BlockCopies.sponge_init domain len = ok s) : Canonical s := by
  obtain ⟨expected,he,hcells⟩ := sponge_init_spec domain len
  have same : s = expected := Result.ok.inj (hs.symm.trans he)
  intro j hj
  rw [same,hcells]
  split_ifs
  · exact hd
  · exact hl
  · change 0 < 2147483647;omega
#print axioms init

theorem absorb (chunk : Array U32 8#usize) (len : Usize)
    (hc : Canon8 chunk) (s : Array U32 16#usize)
    (hs : R0BlockCopies.sponge_absorb chunk len = ok s) : Canonical s := by
  obtain ⟨expected,he,hcells⟩ := sponge_absorb_spec chunk len
  have same : s = expected := Result.ok.inj (hs.symm.trans he)
  intro j hj
  rw [same,hcells]
  split_ifs with hit
  · exact hc j hit.1
  · change 0 < 2147483647;omega
#print axioms absorb

theorem node_pre (right : Array U32 8#usize) (hc : Canon8 right)
    (s : Array U32 16#usize) (hs : R0BlockCopies.node_pre right = ok s) : Canonical s := by
  obtain ⟨expected,he,hcells⟩ := node_pre_spec right hc
  have same : s = expected := Result.ok.inj (hs.symm.trans he)
  intro j hj
  rw [same,hcells]
  have h7 := hc 7 (by omega)
  split_ifs with h8 h15 hsub h16
  · omega
  · omega
  · omega
  · exact hc (j-8) (by omega)
  · omega
#print axioms node_pre

theorem node_absorb (left : Array U32 8#usize) (hc : Canon8 left)
    (s : Array U32 16#usize) (hs : R0BlockCopies.node_absorb left = ok s) : Canonical s := by
  obtain ⟨expected,he,hcells⟩ := node_absorb_spec left
  have same : s = expected := Result.ok.inj (hs.symm.trans he)
  intro j hj
  rw [same,hcells]
  split_ifs with h8
  · exact hc j h8
  · change 0 < 2147483647;omega
#print axioms node_absorb
end PV_L2C_WriterEndsRange
