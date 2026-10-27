import R0Z.BuilderBlocksModel
import R0Z.PoseidonRounds

/-! All 57 blocks without the RoundsOk premise, for the copy (DESIGN-BUILDER-MODEL §11.5 (3)).

`RustWriterCopy v R h` is the copy writer of block h with its permutation
computed by the extracted Poseidon copy: the block's own pre-state and
absorption (node_pre/node_absorb for the 45 node blocks, zeros for a
withdrawal's 27..29, the sponge pre-state and sponge_absorb otherwise) are
fed to `R0PoseidonCopy.perm_rounds`, and its eleven rows are written by
`write_block`.  `builder_blocks_model_copy`: under `BuilderInputLifts` (the
node children's lifts and the sponge pre-state / absorption lifts — the
premises of `builder_blocks_model` other than RoundsOk), every cell of every
block equals `buildModel pub w` at row 16h+l.  RoundsOk is discharged by
`perm_rounds_lift`.  The copy↔production link for the permutation stays the
differential test diff-g (D54.3). -/
set_option autoImplicit false
noncomputable section

namespace R0Z.WriterRefine
open Aeneas Aeneas.Std Result
open R0Z.BuilderModel

variable {K : Type} [Field K]

/-- The Rust inputs of every block, without the permutation rows. -/
structure RustInputs where
  left : Nat → Array U32 8#usize
  right : Nat → Array U32 8#usize
  spre : Nat → Array U32 16#usize
  schunk : Nat → Array U32 8#usize
  sclen : Nat → Usize

/-- The copy writer of block h, permutation included. -/
def RustWriterCopy (v : R0P.Variant) (R : RustInputs) (h : Nat) : Result (Array U32 256#usize) :=
  if NodeKind h then do
    let pre ← R0BlockCopies.node_pre (R.right h)
    let ab ← R0BlockCopies.node_absorb (R.left h)
    let rounds ← R0PoseidonCopy.perm_rounds pre ab
    R0BlockCopies.write_block pre ab rounds
  else if ZeroKind v h then do
    let rounds ← R0PoseidonCopy.perm_rounds zero16 zero16
    R0BlockCopies.write_block zero16 zero16 rounds
  else do
    let ab ← R0BlockCopies.sponge_absorb (R.schunk h) (R.sclen h)
    let rounds ← R0PoseidonCopy.perm_rounds (R.spre h) ab
    R0BlockCopies.write_block (R.spre h) ab rounds

/-- BuilderLifts without the RoundsOk field. -/
structure BuilderInputLifts (pub : R0P.Public K) (w : ModelWitness K) (R : RustInputs) : Prop where
  node : ∀ h : Fin 57, NodeKind h.val → ∃ L Rr : R0P.Digest K, blocksOf pub w h = nodeIn L Rr ∧
    DigestLift (R.left h.val) L ∧ DigestLift (R.right h.val) Rr ∧
    ∀ i, i < 8 → ((R.right h.val).val[i]!).val < 2147483647
  spre : ∀ h : Fin 57, ¬ NodeKind h.val → ¬ ZeroKind pub.variant h.val →
    ∀ i : Fin 16, liftU (K := K) ((R.spre h.val).val[i.val]!) = (blocksOf pub w h).pre i
  sabs : ∀ h : Fin 57, ¬ NodeKind h.val → ¬ ZeroKind pub.variant h.val →
    ∀ i : Fin 16, (blocksOf pub w h).absorb i =
      (if i.val < 8 ∧ i.val < (R.sclen h.val).val then liftU (K := K) ((R.schunk h.val).val[i.val]!) else 0)

theorem builder_blocks_model_copy [CharP K 0x7fffffff] (pub : R0P.Public K) (w : ModelWitness K)
    (R : RustInputs) (hL : BuilderInputLifts pub w R) (h : Fin 57) :
    ∃ b, RustWriterCopy pub.variant R h.val = ok b ∧ ∀ l c : Fin 16,
      liftU (K := K) (b.val[l.val * 16 + c.val]!) =
        buildModel pub w ⟨c.val, by omega⟩ ⟨16 * h.val + l.val, by have := h.isLt; omega⟩ := by
  have cellEq : ∀ (b : Array U32 256#usize),
      (∀ l c : Fin 16, liftU (K := K) (b.val[l.val * 16 + c.val]!) = blockCell (blocksOf pub w h) l.val c) →
      ∀ l c : Fin 16, liftU (K := K) (b.val[l.val * 16 + c.val]!) =
        buildModel pub w ⟨c.val, by omega⟩ ⟨16 * h.val + l.val, by have := h.isLt; omega⟩ := by
    intro b hb l c
    rw [hb l c, buildModel, cell_block _ _ c.isLt h l.val l.isLt _ rfl]
    rfl
  unfold RustWriterCopy
  by_cases hn : NodeKind h.val
  · rw [if_pos hn]
    obtain ⟨L, Rr, he, hl, hr, hc⟩ := hL.node h hn
    obtain ⟨pre, ab, hp, ha, hE⟩ := node_ends_lift (R.left h.val) (R.right h.val) L Rr hl hr hc
    obtain ⟨rounds, hro, hR⟩ := R0Z.PoseidonRefine.perm_rounds_lift pre ab _ hE
    obtain ⟨b, hb, hs⟩ := block_model pre ab rounds _ hE hR
    refine ⟨b, ?_, cellEq b (by rw [he]; exact hs)⟩
    simp only [hp, ha, hro, bind_tc_ok]
    exact hb
  rw [if_neg hn]
  by_cases hz : ZeroKind pub.variant h.val
  · rw [if_pos hz]
    obtain ⟨hv, h1, h2⟩ := hz
    have hzero : blocksOf pub w h = ⟨0, 0⟩ := by
      rw [blocksOf_recip pub w h h1 h2, recipB_wd pub w _ hv]
    have he : EndsLift zero16 zero16 (blocksOf pub w h) := by
      rw [hzero]
      exact ⟨fun i => by show liftU _ = 0; unfold zero16; rw [rep16]; unfold liftU; simp,
        fun i => by show liftU _ = 0; unfold zero16; rw [rep16]; unfold liftU; simp⟩
    obtain ⟨rounds, hro, hR⟩ := R0Z.PoseidonRefine.perm_rounds_lift zero16 zero16 _ he
    obtain ⟨b, hb, hs⟩ := block_model zero16 zero16 rounds _ he hR
    refine ⟨b, ?_, cellEq b hs⟩
    simp only [hro, bind_tc_ok]
    exact hb
  · rw [if_neg hz]
    obtain ⟨ab, hab, habs⟩ := sponge_absorb_spec (R.schunk h.val) (R.sclen h.val)
    have he : EndsLift (R.spre h.val) ab (blocksOf pub w h) := by
      refine ⟨hL.spre h hn hz, fun i => ?_⟩
      rw [hL.sabs h hn hz i, habs]
      by_cases c : i.val < 8 ∧ i.val < (R.sclen h.val).val
      · rw [if_pos c, if_pos c]
      · rw [if_neg c, if_neg c]; unfold liftU; simp
    obtain ⟨rounds, hro, hR⟩ := R0Z.PoseidonRefine.perm_rounds_lift (R.spre h.val) ab _ he
    obtain ⟨b, hb, hs⟩ := block_model (R.spre h.val) ab rounds _ he hR
    refine ⟨b, ?_, cellEq b hs⟩
    simp only [hab, hro, bind_tc_ok]
    exact hb

end R0Z.WriterRefine

#print axioms R0Z.WriterRefine.builder_blocks_model_copy
