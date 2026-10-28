import PV_L2C_ComputedDigestRange
import R1Z.BuilderRecordCanonical
set_option autoImplicit false
namespace PV_L2C_ChunkRange
open Aeneas Aeneas.Std Result R0Z.WriterRefine

theorem note2 (v a : U32) (s : Array U32 8#usize)
    (hv : v.val < 2147483647) (ha : a.val < 2147483647) (hs : Canon8 s) :
    Canon8 (noteC2R v a s) := by
  intro j hj
  rw [noteC2R,arr8_get _ j hj]
  dsimp only
  split_ifs with h0 h1
  · exact hv
  · exact ha
  · exact hs (j-2) (by omega)
#print axioms note2

theorem note3 (s : Array U32 8#usize) (hs : Canon8 s) : Canon8 (noteC3R s) := by
  intro j hj
  rw [noteC3R,arr8_get _ j hj]
  dsimp only
  split_ifs
  · exact hs 6 (by omega)
  · exact hs 7 (by omega)
  · change 0 < 2147483647;omega
#print axioms note3

theorem chunks (w : RustWitness) (p : RustPublic)
    (hw : R1Z.BuilderRecordCanonical.CanonicalWords w) (ha : p.asset.val < 2147483647)
    (h : Nat) : Canon8 ((chunksOf w p).schunk h) := by
  unfold chunksOf
  dsimp only
  split_ifs
  · exact hw.sk
  · exact PV_L2C_ComputedDigestRange.fallback _ (PV_L2C_ComputedDigestRange.owner w)
  · exact note2 _ _ _ (by have := hw.shape.values.1;omega) ha hw.salt
  · exact note3 _ hw.salt
  · exact hw.salt
  · exact hw.recipientOwner
  · exact note2 _ _ _ (by have := hw.shape.values.2.1;omega) ha hw.recipientSalt
  · exact note3 _ hw.recipientSalt
  · exact hw.changeOwner
  · exact note2 _ _ _ (by have := hw.shape.values.2.2;omega) ha hw.changeSalt
  · exact note3 _ hw.changeSalt
  · exact zero8_canon
#print axioms chunks

theorem ordered (a b : Array U32 8#usize) (bit : Bool) (ha : Canon8 a) (hb : Canon8 b) :
    Canon8 (orderedR a b bit).1 ∧ Canon8 (orderedR a b bit).2 := by
  cases bit
  · exact ⟨ha,hb⟩
  · exact ⟨hb,ha⟩
#print axioms ordered

theorem children (w : RustWitness) (p : RustPublic) (hw : WitnessOk w)
    (hf : ∀ n, n < 20 → Canon8 (p.frontier.val[n]!))
    (he : ∀ n, n < 20 → Canon8 (p.empty.val[n]!))
    (h : Nat) (hh : h < 57) :
    Canon8 (childrenOf w p h).1 ∧ Canon8 (childrenOf w p h).2 := by
  unfold childrenOf
  split_ifs with hm hhi hout happ
  · exact ordered _ _ _ (PV_L2C_ComputedDigestRange.fallback _
      (PV_L2C_ComputedDigestRange.tree w p _)) (hw.sibs _ (by omega))
  · exact ordered _ _ _ (PV_L2C_ComputedDigestRange.fallback _
      (PV_L2C_ComputedDigestRange.tree w p _)) (hw.sibs _ (by omega))
  · cases p.variant
    · exact ⟨PV_L2C_ComputedDigestRange.fallback _ (PV_L2C_ComputedDigestRange.note _ _),
        PV_L2C_ComputedDigestRange.fallback _ (PV_L2C_ComputedDigestRange.note _ _)⟩
    · exact ⟨PV_L2C_ComputedDigestRange.fallback _ (PV_L2C_ComputedDigestRange.note _ _),zero8_canon⟩
  · apply ordered _ _ _ (PV_L2C_ComputedDigestRange.fallback _
      (PV_L2C_ComputedDigestRange.append w p _))
    unfold appSibR
    split_ifs
    · exact hf _ (by omega)
    · exact he _ (by omega)
  · exact ⟨zero8_canon,zero8_canon⟩
#print axioms children
end PV_L2C_ChunkRange
