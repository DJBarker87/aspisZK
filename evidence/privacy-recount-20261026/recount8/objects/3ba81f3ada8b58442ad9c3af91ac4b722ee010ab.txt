import R0Z.BuilderBlocksCopy

/-! Sponge chaining for the copy (DESIGN-BUILDER-MODEL §12 (1)).

The sponge pre-states are no longer inputs.  `spongePre R h` is what the Rust
builder computes: sponge_init(domain, len) for the first block of each sponge
(owner 0x41530001/8 at block 0, note 0x41530003/18 at 1, 27, 30, nullifier
0x41530002/16 at 25), and for a chained block the previous block's final
permutation row (rounds[10] of the copy's perm_rounds on the previous
pre-state and absorption).  `builder_blocks_model_chain`: under
`BuilderChunkLifts` (node children and sponge chunk absorptions only), all 57
blocks of `RustWriterChain` equal buildModel. -/
set_option autoImplicit false
noncomputable section

namespace R0Z.WriterRefine
open Aeneas Aeneas.Std Result
open R0Z.BuilderModel

variable {K : Type} [Field K]

/-- The Rust inputs of every block other than permutation rows and sponge pre-states. -/
structure RustChunks where
  left : Nat → Array U32 8#usize
  right : Nat → Array U32 8#usize
  schunk : Nat → Array U32 8#usize
  sclen : Nat → Usize

/-- One chained sponge step: absorb, permute, return the final row. -/
def spongeStep (pre : Array U32 16#usize) (chunk : Array U32 8#usize) (clen : Usize) :
    Result (Array U32 16#usize) := do
  let ab ← R0BlockCopies.sponge_absorb chunk clen
  let rounds ← R0PoseidonCopy.perm_rounds pre ab
  ok rounds.val[10]!

def initOwner : Result (Array U32 16#usize) := R0BlockCopies.sponge_init 0x41530001#u32 8#u32
def initNote : Result (Array U32 16#usize) := R0BlockCopies.sponge_init 0x41530003#u32 18#u32
def initNul : Result (Array U32 16#usize) := R0BlockCopies.sponge_init 0x41530002#u32 16#u32

/-- The Rust sponge pre-state of block h. -/
def spongePre (R : RustChunks) (h : Nat) : Result (Array U32 16#usize) :=
  match h with
  | 0 => initOwner
  | 1 => initNote
  | 2 => do let p ← initNote; spongeStep p (R.schunk 1) (R.sclen 1)
  | 3 => do
      let p ← initNote
      let p ← spongeStep p (R.schunk 1) (R.sclen 1)
      spongeStep p (R.schunk 2) (R.sclen 2)
  | 25 => initNul
  | 26 => do let p ← initNul; spongeStep p (R.schunk 25) (R.sclen 25)
  | 27 => initNote
  | 28 => do let p ← initNote; spongeStep p (R.schunk 27) (R.sclen 27)
  | 29 => do
      let p ← initNote
      let p ← spongeStep p (R.schunk 27) (R.sclen 27)
      spongeStep p (R.schunk 28) (R.sclen 28)
  | 30 => initNote
  | 31 => do let p ← initNote; spongeStep p (R.schunk 30) (R.sclen 30)
  | 32 => do
      let p ← initNote
      let p ← spongeStep p (R.schunk 30) (R.sclen 30)
      spongeStep p (R.schunk 31) (R.sclen 31)
  | _ => ok zero16

/-- The copy writer of block h, permutation and sponge chaining included. -/
def RustWriterChain (v : R0P.Variant) (R : RustChunks) (h : Nat) : Result (Array U32 256#usize) :=
  if NodeKind h then do
    let pre ← R0BlockCopies.node_pre (R.right h)
    let ab ← R0BlockCopies.node_absorb (R.left h)
    let rounds ← R0PoseidonCopy.perm_rounds pre ab
    R0BlockCopies.write_block pre ab rounds
  else if ZeroKind v h then do
    let rounds ← R0PoseidonCopy.perm_rounds zero16 zero16
    R0BlockCopies.write_block zero16 zero16 rounds
  else do
    let pre ← spongePre R h
    let ab ← R0BlockCopies.sponge_absorb (R.schunk h) (R.sclen h)
    let rounds ← R0PoseidonCopy.perm_rounds pre ab
    R0BlockCopies.write_block pre ab rounds

/-- BuilderInputLifts without the sponge pre-states. -/
structure BuilderChunkLifts (pub : R0P.Public K) (w : ModelWitness K) (R : RustChunks) : Prop where
  node : ∀ h : Fin 57, NodeKind h.val → ∃ L Rr : R0P.Digest K, blocksOf pub w h = nodeIn L Rr ∧
    DigestLift (R.left h.val) L ∧ DigestLift (R.right h.val) Rr ∧
    ∀ i, i < 8 → ((R.right h.val).val[i]!).val < 2147483647
  sabs : ∀ h : Fin 57, ¬ NodeKind h.val → ¬ ZeroKind pub.variant h.val →
    ∀ i : Fin 16, (blocksOf pub w h).absorb i =
      (if i.val < 8 ∧ i.val < (R.sclen h.val).val then liftU (K := K) ((R.schunk h.val).val[i.val]!) else 0)

theorem sponge_ends (pre : Array U32 16#usize) (chunk : Array U32 8#usize) (clen : Usize) (B : BlockIn K)
    (hpre : ∀ i : Fin 16, liftU (K := K) (pre.val[i.val]!) = B.pre i)
    (habs : ∀ i : Fin 16, B.absorb i =
      (if i.val < 8 ∧ i.val < clen.val then liftU (K := K) (chunk.val[i.val]!) else 0)) :
    ∃ ab, R0BlockCopies.sponge_absorb chunk clen = ok ab ∧ EndsLift pre ab B := by
  obtain ⟨ab, hab, habs'⟩ := sponge_absorb_spec chunk clen
  refine ⟨ab, hab, hpre, fun i => ?_⟩
  rw [habs i, habs']
  by_cases c : i.val < 8 ∧ i.val < clen.val
  · rw [if_pos c, if_pos c]
  · rw [if_neg c, if_neg c]; unfold liftU; simp

theorem chain_step [CharP K 0x7fffffff] (B B' : BlockIn K) (hB' : B'.pre = blockOut B)
    (pre : Array U32 16#usize) (hpre : ∀ i : Fin 16, liftU (K := K) (pre.val[i.val]!) = B.pre i)
    (chunk : Array U32 8#usize) (clen : Usize)
    (habs : ∀ i : Fin 16, B.absorb i =
      (if i.val < 8 ∧ i.val < clen.val then liftU (K := K) (chunk.val[i.val]!) else 0)) :
    ∃ s, spongeStep pre chunk clen = ok s ∧ ∀ i : Fin 16, liftU (K := K) (s.val[i.val]!) = B'.pre i := by
  obtain ⟨ab, hab, he⟩ := sponge_ends pre chunk clen B hpre habs
  obtain ⟨rounds, hro, hR⟩ := R0Z.PoseidonRefine.perm_rounds_lift pre ab B he
  refine ⟨rounds.val[10]!, ?_, fun i => ?_⟩
  · rw [spongeStep]
    simp only [hab, hro, bind_tc_ok]
  · rw [hB']
    exact hR 10 i (by norm_num)

theorem init_step (dom len : U32) (d l : Nat) [Nat.AtLeastTwo d] [Nat.AtLeastTwo l]
    (hd : dom.val = (OfNat.ofNat d : Nat)) (hl : len.val = (OfNat.ofNat l : Nat)) (B : BlockIn K)
    (hB : B.pre = spongeInit (OfNat.ofNat d) (OfNat.ofNat l)) :
    ∃ s, R0BlockCopies.sponge_init dom len = ok s ∧ ∀ i : Fin 16, liftU (K := K) (s.val[i.val]!) = B.pre i := by
  obtain ⟨s, hs, -⟩ := sponge_init_spec dom len
  refine ⟨s, hs, ?_⟩
  rw [hB]
  exact spre_init dom len _ _ (R0Z.PoseidonRefine.lane_lift d hd rfl)
    (R0Z.PoseidonRefine.lane_lift l hl rfl) s hs

theorem owner_init (B : BlockIn K) (hB : B.pre = spongeInit 0x41530001 8) :
    ∃ s, initOwner = ok s ∧ ∀ i : Fin 16, liftU (K := K) (s.val[i.val]!) = B.pre i :=
  init_step _ _ 0x41530001 8 (UScalar.ofNatCore_val_eq _) (UScalar.ofNatCore_val_eq _) B hB

theorem note_init (B : BlockIn K) (hB : B.pre = spongeInit 0x41530003 18) :
    ∃ s, initNote = ok s ∧ ∀ i : Fin 16, liftU (K := K) (s.val[i.val]!) = B.pre i :=
  init_step _ _ 0x41530003 18 (UScalar.ofNatCore_val_eq _) (UScalar.ofNatCore_val_eq _) B hB

theorem nul_init (B : BlockIn K) (hB : B.pre = spongeInit 0x41530002 16) :
    ∃ s, initNul = ok s ∧ ∀ i : Fin 16, liftU (K := K) (s.val[i.val]!) = B.pre i :=
  init_step _ _ 0x41530002 16 (UScalar.ofNatCore_val_eq _) (UScalar.ofNatCore_val_eq _) B hB

section chain
variable [CharP K 0x7fffffff] (pub : R0P.Public K) (w : ModelWitness K) (R : RustChunks)
  (hL : BuilderChunkLifts pub w R)

include hL in
/-- The sabs premise at a literal sponge block. -/
theorem sabs_at (h : Nat) (hh : h < 57) (hn : ¬ NodeKind h) (hz : ¬ ZeroKind pub.variant h) :
    ∀ i : Fin 16, (blocksOf pub w ⟨h, hh⟩).absorb i =
      (if i.val < 8 ∧ i.val < (R.sclen h).val then liftU (K := K) ((R.schunk h).val[i.val]!) else 0) :=
  hL.sabs ⟨h, hh⟩ hn hz

theorem nk (h : Nat) (h1 : h < 4 ∨ (25 ≤ h ∧ h ≤ 32)) : ¬ NodeKind h := by
  unfold NodeKind; omega

theorem zk (v : R0P.Variant) (h : Nat) (h1 : h < 27 ∨ 29 < h) : ¬ ZeroKind v h := by
  unfold ZeroKind; omega

theorem zk_tr (h : Nat) (hv : pub.variant = .privateTransfer) : ¬ ZeroKind pub.variant h := by
  unfold ZeroKind; rw [hv]; simp

include hL in
/-- Every sponge block's Rust pre-state lifts to the model pre-state. -/
theorem spongePre_lift (h : Fin 57) (hn : ¬ NodeKind h.val) (hz : ¬ ZeroKind pub.variant h.val) :
    ∃ s, spongePre R h.val = ok s ∧ ∀ i : Fin 16, liftU (K := K) (s.val[i.val]!) = (blocksOf pub w h).pre i := by
  obtain ⟨hv, hh⟩ := h
  dsimp only at hn hz ⊢
  have cases : hv = 0 ∨ hv = 1 ∨ hv = 2 ∨ hv = 3 ∨ hv = 25 ∨ hv = 26 ∨ hv = 27 ∨ hv = 28 ∨ hv = 29 ∨
      hv = 30 ∨ hv = 31 ∨ hv = 32 := by
    unfold NodeKind at hn; omega
  -- the chained blocks of each sponge, with their model chaining equalities
  have s1 := note_init (K := K) (blocksOf pub w 1) rfl
  have s0 := owner_init (K := K) (blocksOf pub w 0) rfl
  have s25 := nul_init (K := K) (blocksOf pub w 25) rfl
  have s30 := note_init (K := K) (blocksOf pub w 30) rfl
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s0
  · exact s1
  · obtain ⟨p1, hp1, hv1⟩ := s1
    obtain ⟨p2, hp2, hv2⟩ := chain_step _ _ (pre_2 pub w) p1 hv1 (R.schunk 1) (R.sclen 1)
      (sabs_at pub w R hL 1 (by omega) (nk 1 (by omega)) (zk _ 1 (by omega)))
    exact ⟨p2, by simp only [spongePre, hp1, bind_tc_ok, hp2], hv2⟩
  · obtain ⟨p1, hp1, hv1⟩ := s1
    obtain ⟨p2, hp2, hv2⟩ := chain_step _ _ (pre_2 pub w) p1 hv1 (R.schunk 1) (R.sclen 1)
      (sabs_at pub w R hL 1 (by omega) (nk 1 (by omega)) (zk _ 1 (by omega)))
    obtain ⟨p3, hp3, hv3⟩ := chain_step _ _ (pre_3 pub w) p2 hv2 (R.schunk 2) (R.sclen 2)
      (sabs_at pub w R hL 2 (by omega) (nk 2 (by omega)) (zk _ 2 (by omega)))
    exact ⟨p3, by simp only [spongePre, hp1, bind_tc_ok, hp2, hp3], hv3⟩
  · exact s25
  · obtain ⟨p1, hp1, hv1⟩ := s25
    obtain ⟨p2, hp2, hv2⟩ := chain_step _ _ (pre_26 pub w) p1 hv1 (R.schunk 25) (R.sclen 25)
      (sabs_at pub w R hL 25 (by omega) (nk 25 (by omega)) (zk _ 25 (by omega)))
    exact ⟨p2, by simp only [spongePre, hp1, bind_tc_ok, hp2], hv2⟩
  · have htr : pub.variant = .privateTransfer := by
      cases e : pub.variant
      · rfl
      · exact absurd ⟨e, by omega, by omega⟩ hz
    exact note_init (K := K) (blocksOf pub w 27) (by
      show (recipB pub w 0).pre = _; unfold recipB; rw [htr]; rfl)
  · have htr : pub.variant = .privateTransfer := by
      cases e : pub.variant
      · rfl
      · exact absurd ⟨e, by omega, by omega⟩ hz
    obtain ⟨p1, hp1, hv1⟩ := note_init (K := K) (blocksOf pub w 27) (by
      show (recipB pub w 0).pre = _; unfold recipB; rw [htr]; rfl)
    obtain ⟨p2, hp2, hv2⟩ := chain_step _ _ (pre_28 pub w htr) p1 hv1 (R.schunk 27) (R.sclen 27)
      (sabs_at pub w R hL 27 (by omega) (nk 27 (by omega)) (zk_tr pub 27 htr))
    exact ⟨p2, by simp only [spongePre, hp1, bind_tc_ok, hp2], hv2⟩
  · have htr : pub.variant = .privateTransfer := by
      cases e : pub.variant
      · rfl
      · exact absurd ⟨e, by omega, by omega⟩ hz
    obtain ⟨p1, hp1, hv1⟩ := note_init (K := K) (blocksOf pub w 27) (by
      show (recipB pub w 0).pre = _; unfold recipB; rw [htr]; rfl)
    obtain ⟨p2, hp2, hv2⟩ := chain_step _ _ (pre_28 pub w htr) p1 hv1 (R.schunk 27) (R.sclen 27)
      (sabs_at pub w R hL 27 (by omega) (nk 27 (by omega)) (zk_tr pub 27 htr))
    obtain ⟨p3, hp3, hv3⟩ := chain_step _ _ (pre_29 pub w htr) p2 hv2 (R.schunk 28) (R.sclen 28)
      (sabs_at pub w R hL 28 (by omega) (nk 28 (by omega)) (zk_tr pub 28 htr))
    exact ⟨p3, by simp only [spongePre, hp1, bind_tc_ok, hp2, hp3], hv3⟩
  · exact s30
  · obtain ⟨p1, hp1, hv1⟩ := s30
    obtain ⟨p2, hp2, hv2⟩ := chain_step _ _ (pre_31 pub w) p1 hv1 (R.schunk 30) (R.sclen 30)
      (sabs_at pub w R hL 30 (by omega) (nk 30 (by omega)) (zk _ 30 (by omega)))
    exact ⟨p2, by simp only [spongePre, hp1, bind_tc_ok, hp2], hv2⟩
  · obtain ⟨p1, hp1, hv1⟩ := s30
    obtain ⟨p2, hp2, hv2⟩ := chain_step _ _ (pre_31 pub w) p1 hv1 (R.schunk 30) (R.sclen 30)
      (sabs_at pub w R hL 30 (by omega) (nk 30 (by omega)) (zk _ 30 (by omega)))
    obtain ⟨p3, hp3, hv3⟩ := chain_step _ _ (pre_32 pub w) p2 hv2 (R.schunk 31) (R.sclen 31)
      (sabs_at pub w R hL 31 (by omega) (nk 31 (by omega)) (zk _ 31 (by omega)))
    exact ⟨p3, by simp only [spongePre, hp1, bind_tc_ok, hp2, hp3], hv3⟩

include hL in
theorem builder_blocks_model_chain (h : Fin 57) :
    ∃ b, RustWriterChain pub.variant R h.val = ok b ∧ ∀ l c : Fin 16,
      liftU (K := K) (b.val[l.val * 16 + c.val]!) =
        buildModel pub w ⟨c.val, by omega⟩ ⟨16 * h.val + l.val, by have := h.isLt; omega⟩ := by
  let RI : RustInputs := ⟨R.left, R.right, fun h => match spongePre R h with
    | ok s => s | _ => zero16, R.schunk, R.sclen⟩
  have hI : BuilderInputLifts pub w RI := by
    refine ⟨hL.node, fun h hn hz => ?_, hL.sabs⟩
    obtain ⟨s, hs, hsv⟩ := spongePre_lift pub w R hL h hn hz
    intro i
    show liftU ((match spongePre R h.val with | ok s => s | _ => zero16).val[i.val]!) = _
    rw [hs]
    exact hsv i
  obtain ⟨b, hb, hcells⟩ := builder_blocks_model_copy pub w RI hI h
  refine ⟨b, ?_, hcells⟩
  unfold RustWriterChain
  unfold RustWriterCopy at hb
  by_cases hn : NodeKind h.val
  · rw [if_pos hn] at hb ⊢; exact hb
  rw [if_neg hn] at hb ⊢
  by_cases hz : ZeroKind pub.variant h.val
  · rw [if_pos hz] at hb ⊢; exact hb
  rw [if_neg hz] at hb ⊢
  obtain ⟨s, hs, -⟩ := spongePre_lift pub w R hL h hn hz
  have e : RI.spre h.val = s := by show (match spongePre R h.val with | ok s => s | _ => zero16) = s; rw [hs]
  rw [e] at hb
  rw [hs]
  simp only [bind_tc_ok]
  exact hb

end chain

#print axioms R0Z.WriterRefine.chain_step
#print axioms R0Z.WriterRefine.spongePre_lift
#print axioms R0Z.WriterRefine.builder_blocks_model_chain
end R0Z.WriterRefine
