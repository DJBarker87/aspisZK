import PV_L2C_CanonicalCaller
import R0Z.PoseidonCanon
set_option autoImplicit false
namespace PV_L2C_BlockRange
open Aeneas Aeneas.Std Result R0Z.WriterRefine

def Canonical {n : Usize} (a : Array U32 n) : Prop :=
  ∀ k, k < n.val → (a.val[k]!).val < 2147483647

theorem zeros (n : Usize) : Canonical (Array.repeat n 0#u32) := by
  intro k hk
  rw [Array.repeat_val,List.getElem!_eq_getElem?_getD,List.getElem?_replicate,if_pos hk]
  change 0 < 2147483647
  omega
#print axioms zeros

theorem fallback {n : Usize} (r : Result (Array U32 n)) (d : Array U32 n)
    (hd : Canonical d) (hr : ∀ out, r = ok out → Canonical out) :
    Canonical (okOr r d) := by
  cases r <;> first | exact hr _ rfl | exact hd
#print axioms fallback

/-- Exact raw cell bounds of the extracted block writer, before projection
to a field. The pre-state and absorption cells are included. -/
theorem block (pre ab : Array U32 16#usize)
    (rounds : Array (Array U32 16#usize) 11#usize) (b : Array U32 256#usize)
    (hp : Canonical pre) (ha : Canonical ab)
    (hr : R0PoseidonCopy.perm_rounds pre ab = ok rounds)
    (hb : R0BlockCopies.write_block pre ab rounds = ok b) : Canonical b := by
  obtain ⟨expected,he,hcells⟩ := block_spec pre ab rounds
  have same : b = expected := Result.ok.inj (hb.symm.trans he)
  intro k hk
  rw [same,hcells]
  unfold BlockVal
  split_ifs with hpre hround hab
  · exact hp k (by simpa using hpre)
  · exact R0Z.PoseidonRefine.perm_canon pre ab rounds hr (k/16-1)
      (by omega) (k%16) (by omega)
  · exact ha (k-192) (by simp;omega)
  · change 0 < 2147483647
    omega
#print axioms block

theorem digest (pre ab : Array U32 16#usize) (d : Array U32 8#usize)
    (h : blockDigestR pre ab = ok d) : Canon8 d := by
  unfold blockDigestR at h
  pv_peel h with rounds hr
  cases h
  intro j hj
  rw [digest8_get _ j hj]
  exact R0Z.PoseidonRefine.perm_canon pre ab rounds hr 10 (by omega) j (by omega)
#print axioms digest

theorem sponge_digest (pre : Array U32 16#usize) (chunk : Array U32 8#usize)
    (len : Usize) (d : Array U32 8#usize)
    (h : spongeDigestR pre chunk len = ok d) : Canon8 d := by
  unfold spongeDigestR at h
  pv_peel h with ab hab
  exact digest pre ab d h
#print axioms sponge_digest

theorem node_digest (left right d : Array U32 8#usize)
    (h : nodeDigestR left right = ok d) : Canon8 d := by
  unfold nodeDigestR at h
  pv_peel h with pre hp
  pv_peel h with ab ha
  exact digest pre ab d h
#print axioms node_digest

theorem sponge_step (pre : Array U32 16#usize) (chunk : Array U32 8#usize)
    (len : Usize) (s : Array U32 16#usize)
    (h : spongeStep pre chunk len = ok s) : Canonical s := by
  unfold spongeStep at h
  pv_peel h with ab ha
  pv_peel h with rounds hr
  cases h
  intro j hj
  exact R0Z.PoseidonRefine.perm_canon pre ab rounds hr 10 (by omega) j
    (by simpa using hj)
#print axioms sponge_step
end PV_L2C_BlockRange
