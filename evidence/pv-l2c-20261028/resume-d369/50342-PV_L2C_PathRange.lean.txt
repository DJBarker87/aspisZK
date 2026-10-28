import PV_L2C_BlockRange
import R0Z.WriterRefinePathBlock
set_option autoImplicit false
namespace PV_L2C_PathRange
open Aeneas Aeneas.Std Result R0Z.WriterRefine PV_L2C_BlockRange

theorem cell (bit dflt : U32) (cur left right : Array U32 8#usize) (lev k : Nat)
    (hb : bit.val < 2147483647) (hd : dflt.val < 2147483647)
    (hc : Canon8 cur) (hl : Canon8 left) (hr : Canon8 right) :
    (PV bit cur left right lev dflt k).val < 2147483647 := by
  unfold PV
  split_ifs with h0 h1 h2 h3
  · exact hb
  · exact hc _ (by omega)
  · exact hl _ (by omega)
  · exact hr _ (by omega)
  · exact hd
#print axioms cell

theorem loop (bits : Array U32 24#usize)
    (cur left right : Array (Array U32 8#usize) 24#usize)
    (hb : ∀ j, j < 24 → (bits.val[j]!).val < 2147483647)
    (hc : ∀ j, j < 24 → Canon8 (cur.val[j]!))
    (hl : ∀ j, j < 24 → Canon8 (left.val[j]!))
    (hr : ∀ j, j < 24 → Canon8 (right.val[j]!))
    (n : Nat) (lev : Usize) (buf out : Array U32 1536#usize)
    (hn : lev.val+n = 24) (hbuf : Canonical buf)
    (hout : R0WriterCopies.write_path_block_loop bits cur left right buf lev = ok out) :
    Canonical out := by
  obtain ⟨expected,he,hcells⟩ := path_block_loop bits cur left right n lev buf hn
  have same : out = expected := Result.ok.inj (hout.symm.trans he)
  intro k hk
  rw [same,hcells]
  split_ifs with hit
  · exact cell _ _ _ _ _ _ _ (hb _ hit.2.2) (hbuf k hk)
      (hc _ hit.2.2) (hl _ hit.2.2) (hr _ hit.2.2)
  · exact hbuf k hk
#print axioms loop
end PV_L2C_PathRange
