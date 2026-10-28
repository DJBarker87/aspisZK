import PV_L2C_WriterEndsRange
import PV_L2C_ChunkRange
set_option autoImplicit false
namespace PV_L2C_WriterChainRange
open Aeneas Aeneas.Std Result R0Z.WriterRefine PV_L2C_BlockRange

theorem pre (r : RustChunks) (n : Nat) (s : Array U32 16#usize)
    (hs : spongePre r n = ok s) : Canonical s := by
  unfold spongePre at hs
  split at hs
  all_goals first
  | exact PV_L2C_WriterEndsRange.init _ _ (by scalar_tac) (by scalar_tac) s hs
  | (pv_peel hs with prior hp
     exact sponge_step _ _ _ _ hs)
  | (pv_peel hs with prior hp
     pv_peel hs with prior2 hp2
     exact sponge_step _ _ _ _ hs)
  | (cases hs; exact zeros 16#usize)
#print axioms pre

theorem chain (v : R0P.Variant) (r : RustChunks) (n : Nat)
    (hl : Canon8 (r.left n)) (hr : Canon8 (r.right n)) (hc : Canon8 (r.schunk n))
    (b : Array U32 256#usize) (hb : RustWriterChain v r n = ok b) : Canonical b := by
  unfold RustWriterChain at hb
  split_ifs at hb with hn hz
  · pv_peel hb with pre hp
    pv_peel hb with ab ha
    pv_peel hb with rounds hrounds
    exact block pre ab rounds b (PV_L2C_WriterEndsRange.node_pre _ hr _ hp)
      (PV_L2C_WriterEndsRange.node_absorb _ hl _ ha) hrounds hb
  · pv_peel hb with rounds hrounds
    exact block zero16 zero16 rounds b (zeros 16#usize) (zeros 16#usize) hrounds hb
  · pv_peel hb with spre hp
    pv_peel hb with ab ha
    pv_peel hb with rounds hrounds
    exact block spre ab rounds b (pre r n spre hp)
      (PV_L2C_WriterEndsRange.absorb _ _ hc _ ha) hrounds hb
#print axioms chain

theorem records (w : RustWitness) (p : RustPublic)
    (hw : R1Z.BuilderRecordCanonical.CanonicalWords w) (ha : p.asset.val < 2147483647)
    (hf : ∀ n, n < 20 → Canon8 (p.frontier.val[n]!))
    (he : ∀ n, n < 20 → Canon8 (p.empty.val[n]!))
    (n : Nat) (hn : n < 57) (b : Array U32 256#usize)
    (hb : RustWriterChain p.variant (rustChunks w p) n = ok b) : Canonical b := by
  have hchildren := PV_L2C_ChunkRange.children w p hw.shape hf he n hn
  exact chain _ _ _ hchildren.1 hchildren.2 (PV_L2C_ChunkRange.chunks w p hw ha n) b hb
#print axioms records
end PV_L2C_WriterChainRange
