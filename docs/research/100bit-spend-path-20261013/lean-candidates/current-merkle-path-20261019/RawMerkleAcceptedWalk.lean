import RawMerklePathWalk

/-! Successful emitted checker acceptance supplies a six-step source walk to
exactly the advertised root and zero final index. The generic equality proof is
reused from ExtractedTerminalEquality without its unrelated validator imports. -/
set_option autoImplicit false
namespace AspisR1MerklePathChildren.RawMerkleAcceptedWalk
open Aeneas Aeneas.Std Result WP
open RawMerklePathWalk

local instance {α : Type} [DecidableEq α] {n : Usize} : DecidableEq (Array α n) :=
  inferInstanceAs (DecidableEq {l : List α // l.length = n.val})

private theorem array_eq_value {α : Type} [DecidableEq α] {n : Usize}
    (cmp : core.cmp.PartialEq α α)
    (hne : ∀ x y, cmp.ne x y ⦃ b => b ↔ x ≠ y ⦄) (a b : Array α n) :
    core.array.equality.PartialEqArray.eq cmp a b = ok (decide (a = b)) := by
  have hs := core.slice.cmp.PartialEqSlice.eq_homo_spec cmp a.to_slice b.to_slice hne
  change WP.spec (core.array.equality.PartialEqArray.eq cmp a b)
    (fun v => v ↔ a.to_slice = b.to_slice) at hs
  obtain ⟨v,hv,hp⟩ := spec_imp_exists hs
  have he : a.to_slice = b.to_slice ↔ a = b := by
    constructor
    · intro h; apply Subtype.ext; exact congrArg (fun x : Slice α => x.val) h
    · intro h; exact congrArg Array.to_slice h
  have hp : v ↔ a = b := hp.trans he
  have hv' : v = decide (a = b) := by cases v <;> simp_all
  simpa only [hv'] using hv

private theorem u8_ne_spec (x y : U8) :
    core.cmp.PartialEqU8.ne x y ⦃ b => b ↔ x ≠ y ⦄ := by
  change WP.spec (ok (decide (x ≠ y))) _
  simp only [WP.spec_ok,decide_eq_true_eq]

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- The path loop, root equality and final-index check are all consequences of
the same actual successful Boolean acceptance. -/
theorem accepted_walk {H : Type} (D : Digest32 H) (hash : H)
    (root : Digest) (index : Usize) (node : Digest) (path : Slice U8)
    (h : verifier.merkle_path D hash root index node path = ok true) :
    Walk D hash path 6 0 index node 0#usize root := by
  unfold verifier.merkle_path at h
  obtain ⟨⟨outIndex,outNode⟩,hloop,h⟩ := bind_success _ _ _ h
  change (do
    let b ← core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 outNode root
    if b then ok (decide (outIndex = 0#usize)) else ok false) = ok true at h
  rw [array_eq_value core.cmp.PartialEqU8 u8_ne_spec] at h
  simp only [bind_tc_ok] at h
  by_cases he : outNode = root
  · simp only [he,decide_true,ite_true] at h
    have hi : outIndex = 0#usize := of_decide_eq_true (Result.ok.inj h)
    subst outIndex
    subst outNode
    exact loop_success_walk D hash path 6 {start := 0#usize, «end» := 6#usize}
      index node 0#usize root rfl rfl hloop
  · simp only [he,decide_false,ite_false] at h
    cases h

#print axioms accepted_walk
end AspisR1MerklePathChildren.RawMerkleAcceptedWalk
