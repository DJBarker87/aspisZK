import PV_L2C_BlockRange
set_option autoImplicit false
namespace PV_L2C_ComputedDigestRange
open Aeneas Aeneas.Std Result R0Z.WriterRefine

theorem fallback (r : Result (Array U32 8#usize))
    (hr : ∀ d, r = ok d → Canon8 d) : Canon8 (okOr r zero8) := by
  have hz : PV_L2C_BlockRange.Canonical zero8 := by
    intro j hj;exact zero8_canon j (by simpa using hj)
  have hc := PV_L2C_BlockRange.fallback r zero8 hz (fun d hd j hj =>
    hr d hd j (by simpa using hj))
  intro j hj
  exact hc j (by simpa using hj)
#print axioms fallback

theorem owner (w : RustWitness) (d : Array U32 8#usize) (h : ownerD w = ok d) :
    Canon8 d := by
  unfold ownerD at h
  pv_peel h with pre hp
  exact PV_L2C_BlockRange.sponge_digest pre w.sk 8#usize d h
#print axioms owner

theorem note (chunks : RustChunks) (block : Nat) (d : Array U32 8#usize)
    (h : noteDigestR chunks block = ok d) : Canon8 d := by
  unfold noteDigestR at h
  pv_peel h with pre hp
  exact PV_L2C_BlockRange.sponge_digest pre (chunks.schunk block) (chunks.sclen block) d h
#print axioms note

/-- The raw output of every computed path digest is canonical even before
assuming raw canonicality of the absorption cells recorded elsewhere. -/
theorem tree (w : RustWitness) (p : RustPublic) (n : Nat) (d : Array U32 8#usize)
    (h : treeCurR w p n = ok d) : Canon8 d := by
  cases n with
  | zero => exact note (chunksOf w p) 3 d h
  | succ n =>
    rw [treeCurR] at h
    pv_peel h with current hc
    exact PV_L2C_BlockRange.node_digest _ _ d h
#print axioms tree

theorem output_pair (w : RustWitness) (p : RustPublic) (d : Array U32 8#usize)
    (h : outPairR w p = ok d) : Canon8 d := by
  unfold outPairR at h
  cases hv : p.variant with
  | privateTransfer =>
    rw [hv] at h
    pv_peel h with recipient hr
    pv_peel h with change hc
    exact PV_L2C_BlockRange.node_digest recipient change d h
  | withdrawal =>
    rw [hv] at h
    pv_peel h with change hc
    exact PV_L2C_BlockRange.node_digest change zero8 d h
#print axioms output_pair

theorem append (w : RustWitness) (p : RustPublic) (n : Nat) (d : Array U32 8#usize)
    (h : appCurR w p n = ok d) : Canon8 d := by
  cases n with
  | zero => exact output_pair w p d h
  | succ n =>
    rw [appCurR] at h
    pv_peel h with current hc
    exact PV_L2C_BlockRange.node_digest _ _ d h
#print axioms append
end PV_L2C_ComputedDigestRange
