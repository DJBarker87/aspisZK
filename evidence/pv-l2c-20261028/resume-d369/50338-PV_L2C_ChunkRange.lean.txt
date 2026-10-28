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
  change Canon8 (if h = 0 ∨ h = 25 then w.sk else if h = 1 then okOr (ownerD w) zero8 else if h = 2 then noteC2R w.inputValue p.asset w.salt else if h = 3 then noteC3R w.salt else if h = 26 then w.salt else if h = 27 then w.recipientOwner else if h = 28 then noteC2R w.outputValue p.asset w.recipientSalt else if h = 29 then noteC3R w.recipientSalt else if h = 30 then w.changeOwner else if h = 31 then noteC2R w.changeValue p.asset w.changeSalt else if h = 32 then noteC3R w.changeSalt else zero8)
  by_cases h0 : h = 0 ∨ h = 25
  · rw [if_pos h0]
    exact hw.sk
  rw [if_neg h0]
  by_cases h1 : h = 1
  · rw [if_pos h1]
    exact PV_L2C_ComputedDigestRange.fallback _ (PV_L2C_ComputedDigestRange.owner w)
  rw [if_neg h1]
  by_cases h2 : h = 2
  · rw [if_pos h2]
    exact note2 _ _ _ (by have := hw.shape.values.1;omega) ha hw.salt
  rw [if_neg h2]
  by_cases h3 : h = 3
  · rw [if_pos h3]
    exact note3 _ hw.salt
  rw [if_neg h3]
  by_cases h4 : h = 26
  · rw [if_pos h4]
    exact hw.salt
  rw [if_neg h4]
  by_cases h5 : h = 27
  · rw [if_pos h5]
    exact hw.recipientOwner
  rw [if_neg h5]
  by_cases h6 : h = 28
  · rw [if_pos h6]
    exact note2 _ _ _ (by have := hw.shape.values.2.1;omega) ha hw.recipientSalt
  rw [if_neg h6]
  by_cases h7 : h = 29
  · rw [if_pos h7]
    exact note3 _ hw.recipientSalt
  rw [if_neg h7]
  by_cases h8 : h = 30
  · rw [if_pos h8]
    exact hw.changeOwner
  rw [if_neg h8]
  by_cases h9 : h = 31
  · rw [if_pos h9]
    exact note2 _ _ _ (by have := hw.shape.values.2.2;omega) ha hw.changeSalt
  rw [if_neg h9]
  by_cases h10 : h = 32
  · rw [if_pos h10]
    exact note3 _ hw.changeSalt
  rw [if_neg h10]
  exact zero8_canon
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
