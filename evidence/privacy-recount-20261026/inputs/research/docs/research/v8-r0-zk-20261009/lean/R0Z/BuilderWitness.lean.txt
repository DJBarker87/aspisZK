import R0Z.BuilderBlocksChain
import R0Z.PoseidonCanon

/-! The witness-level Rust-copy builder, part 1: records, the named witness map,
sponge chunks and sponge digests (DESIGN-BUILDER-MODEL §12 (2)).

`RustWitness` / `RustPublic` are u32-level records with the fields the Rust
builder reads (pair_trace.rs build_transfer_inner / build_withdrawal_inner,
pair_forest_trace.rs for levels 21..23).  `toModel` is the named map to
`ModelWitness`, field by field (`liftU` on every word, values as naturals,
directions as `bit ≠ 0`); `PubCorr` states the public-input correspondences.
The sponge chunks of every sponge block are computed from the records
(`chunksOf`), the owner digest from the copy's block-0 permutation, and the
input-leaf / recipient / change note digests from the chained sponge blocks. -/
set_option autoImplicit false
noncomputable section

namespace R0Z.WriterRefine
open Aeneas Aeneas.Std Result
open R0Z.BuilderModel

/-! ### Records and the named map -/

structure RustWitness where
  inputValue : U32
  outputValue : U32
  changeValue : U32
  sk : Array U32 8#usize
  salt : Array U32 8#usize
  bits : Array U32 24#usize
  sibs : Array (Array U32 8#usize) 24#usize
  pairFirst : Array U32 8#usize
  pairOccupied : U32
  pairSecond : Array U32 8#usize
  pairInverse : U32
  recipientOwner : Array U32 8#usize
  recipientSalt : Array U32 8#usize
  changeOwner : Array U32 8#usize
  changeSalt : Array U32 8#usize

structure RustPublic where
  variant : R0P.Variant
  asset : U32
  nextPairIndex : Nat
  frontier : Array (Array U32 8#usize) 20#usize
  empty : Array (Array U32 8#usize) 20#usize

variable {K : Type} [Field K]

/-- A Rust digest as a model digest. -/
def digK (d : Array U32 8#usize) : R0P.Digest K := fun i => liftU (d.val[i.val]!)

def val30 (x : U32) : Fin (2 ^ 30) := ⟨x.val % 2 ^ 30, Nat.mod_lt _ (by norm_num)⟩

/-- **The named witness map** (Rust witness record → ModelWitness). -/
def toModel (W : RustWitness) : ModelWitness K where
  inputValue := val30 W.inputValue
  outputValue := val30 W.outputValue
  changeValue := val30 W.changeValue
  sk := digK W.sk
  salt := digK W.salt
  path := fun l => (decide ((W.bits.val[l.val]!).val ≠ 0), digK (W.sibs.val[l.val]!))
  pairFirst := digK W.pairFirst
  pairOccupied := liftU W.pairOccupied
  pairSecond := digK W.pairSecond
  pairInverse := liftU W.pairInverse
  recipientOwner := digK W.recipientOwner
  recipientSalt := digK W.recipientSalt
  changeOwner := digK W.changeOwner
  changeSalt := digK W.changeSalt

def Canon8 (d : Array U32 8#usize) : Prop := ∀ i, i < 8 → (d.val[i]!).val < 2147483647

/-- Public-input correspondences (named). -/
structure PubCorr (P : RustPublic) (pub : R0P.Public K) : Prop where
  variant : P.variant = pub.variant
  asset : liftU (K := K) P.asset = pub.assetId
  next : P.nextPairIndex = pub.nextPairIndex
  frontier : ∀ l : Fin 20, DigestLift (P.frontier.val[l.val]!) (pub.snapshotFrontier l)
  empty : ∀ l : Fin 20, DigestLift (P.empty.val[l.val]!) (emptyRootK (K := K) l)
  frontierCanon : ∀ l : Fin 20, Canon8 (P.frontier.val[l.val]!)
  emptyCanon : ∀ l : Fin 20, Canon8 (P.empty.val[l.val]!)

/-- Rust-side range facts of the witness record. -/
structure WitnessOk (W : RustWitness) : Prop where
  values : W.inputValue.val < 2 ^ 30 ∧ W.outputValue.val < 2 ^ 30 ∧ W.changeValue.val < 2 ^ 30
  bits : ∀ l, l < 24 → (W.bits.val[l]!).val = 0 ∨ (W.bits.val[l]!).val = 1
  sibs : ∀ l, l < 24 → Canon8 (W.sibs.val[l]!)

/-! ### Small arrays -/

def arr8 (f : Fin 8 → U32) : Array U32 8#usize := ⟨List.ofFn f, by simp⟩

theorem arr8_get (f : Fin 8 → U32) (i : Nat) (h : i < 8) : (arr8 f).val[i]! = f ⟨i, h⟩ := by
  show (List.ofFn f)[i]! = _
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_ofFn, dif_pos h]
  rfl

def zero8 : Array U32 8#usize := arr8 (fun _ => 0#u32)

/-- The first eight lanes of a state. -/
def digest8 (s : Array U32 16#usize) : Array U32 8#usize := arr8 (fun i => s.val[i.val]!)

theorem digest8_get (s : Array U32 16#usize) (i : Nat) (h : i < 8) : (digest8 s).val[i]! = s.val[i]! :=
  arr8_get _ i h

def okOr {α : Type} (r : Result α) (d : α) : α := match r with
  | ok a => a
  | _ => d

theorem okOr_ok {α : Type} (a d : α) : okOr (ok a) d = a := rfl

/-! ### Digests of copy blocks -/

def blockDigestR (pre ab : Array U32 16#usize) : Result (Array U32 8#usize) := do
  let rounds ← R0PoseidonCopy.perm_rounds pre ab
  ok (digest8 rounds.val[10]!)

def spongeDigestR (pre : Array U32 16#usize) (chunk : Array U32 8#usize) (clen : Usize) :
    Result (Array U32 8#usize) := do
  let ab ← R0BlockCopies.sponge_absorb chunk clen
  blockDigestR pre ab

def nodeDigestR (left right : Array U32 8#usize) : Result (Array U32 8#usize) := do
  let pre ← R0BlockCopies.node_pre right
  let ab ← R0BlockCopies.node_absorb left
  blockDigestR pre ab

variable [CharP K 0x7fffffff]

theorem blockDigest_lift (pre ab : Array U32 16#usize) (B : BlockIn K) (he : EndsLift pre ab B) :
    ∃ d, blockDigestR pre ab = ok d ∧ DigestLift d (blockDigest B) ∧ Canon8 d := by
  obtain ⟨rounds, hro, hR⟩ := R0Z.PoseidonRefine.perm_rounds_lift pre ab B he
  have hc := R0Z.PoseidonRefine.perm_canon pre ab rounds hro 10 (by norm_num)
  refine ⟨digest8 rounds.val[10]!, by rw [blockDigestR]; simp only [hro, bind_tc_ok], ?_, ?_⟩
  · exact digest_from_rounds rounds B hR _ (fun i hi => digest8_get _ i hi)
  · intro i hi; rw [digest8_get _ i hi]; exact hc i (by omega)

theorem spongeDigest_lift (pre : Array U32 16#usize) (chunk : Array U32 8#usize) (clen : Usize) (B : BlockIn K)
    (hpre : ∀ i : Fin 16, liftU (K := K) (pre.val[i.val]!) = B.pre i)
    (habs : ∀ i : Fin 16, B.absorb i =
      (if i.val < 8 ∧ i.val < clen.val then liftU (K := K) (chunk.val[i.val]!) else 0)) :
    ∃ d, spongeDigestR pre chunk clen = ok d ∧ DigestLift d (blockDigest B) ∧ Canon8 d := by
  obtain ⟨ab, hab, he⟩ := sponge_ends pre chunk clen B hpre habs
  obtain ⟨d, hd, hdl, hdc⟩ := blockDigest_lift pre ab B he
  exact ⟨d, by rw [spongeDigestR]; simp only [hab, bind_tc_ok, hd], hdl, hdc⟩

theorem nodeDigest_lift (left right : Array U32 8#usize) (L Rr : R0P.Digest K)
    (hl : DigestLift left L) (hr : DigestLift right Rr) (hc : Canon8 right) :
    ∃ d, nodeDigestR left right = ok d ∧ DigestLift d (blockDigest (nodeIn L Rr)) ∧ Canon8 d := by
  obtain ⟨pre, ab, hp, ha, he⟩ := node_ends_lift left right L Rr hl hr hc
  obtain ⟨d, hd, hdl, hdc⟩ := blockDigest_lift pre ab _ he
  exact ⟨d, by rw [nodeDigestR]; simp only [hp, ha, bind_tc_ok, hd], hdl, hdc⟩

/-! ### Chunks -/

def noteC2R (value asset : U32) (salt : Array U32 8#usize) : Array U32 8#usize :=
  arr8 (fun j => if j.val = 0 then value else if j.val = 1 then asset else salt.val[j.val - 2]!)

def noteC3R (salt : Array U32 8#usize) : Array U32 8#usize :=
  arr8 (fun j => if j.val = 0 then salt.val[6]! else if j.val = 1 then salt.val[7]! else 0#u32)

def ownerD (W : RustWitness) : Result (Array U32 8#usize) := do
  let p ← initOwner
  spongeDigestR p W.sk 8#usize

/-- The sponge chunks and lengths of every sponge block (node children filled later). -/
def chunksOf (W : RustWitness) (P : RustPublic) : RustChunks where
  left := fun _ => zero8
  right := fun _ => zero8
  schunk := fun h =>
    if h = 0 ∨ h = 25 then W.sk
    else if h = 1 then okOr (ownerD W) zero8
    else if h = 2 then noteC2R W.inputValue P.asset W.salt
    else if h = 3 then noteC3R W.salt
    else if h = 26 then W.salt
    else if h = 27 then W.recipientOwner
    else if h = 28 then noteC2R W.outputValue P.asset W.recipientSalt
    else if h = 29 then noteC3R W.recipientSalt
    else if h = 30 then W.changeOwner
    else if h = 31 then noteC2R W.changeValue P.asset W.changeSalt
    else if h = 32 then noteC3R W.changeSalt
    else zero8
  sclen := fun h => if h = 3 ∨ h = 29 ∨ h = 32 then 2#usize else 8#usize

theorem n8 : (8#usize : Usize).val = 8 := by simp
theorem n2 : (2#usize : Usize).val = 2 := by simp

theorem sabs_c2 (value asset : U32) (salt : Array U32 8#usize) (v a : K) (s : R0P.Digest K)
    (hv : liftU value = v) (ha : liftU asset = a) (hs : DigestLift salt s) (clen : Usize) (hc : clen.val = 8) :
    ∀ i : Fin 16, noteC2 v a s i =
      (if i.val < 8 ∧ i.val < clen.val then liftU (K := K) ((noteC2R value asset salt).val[i.val]!) else 0) := by
  intro i
  rw [hc]
  unfold noteC2
  by_cases h8 : i.val < 8
  · rw [if_pos (show i.val < 8 ∧ i.val < 8 from ⟨h8, h8⟩), noteC2R, arr8_get _ _ h8]
    dsimp only
    by_cases e0 : i.val = 0
    · rw [if_pos e0, if_pos e0, hv]
    rw [if_neg e0, if_neg e0]
    by_cases e1 : i.val = 1
    · rw [if_pos e1, if_pos e1, ha]
    rw [if_neg e1, if_neg e1, dif_pos h8]
    exact (hs ⟨i.val - 2, by omega⟩).symm
  · rw [if_neg (show ¬ (i.val < 8 ∧ i.val < 8) from fun h => h8 h.1),
      if_neg (show ¬ i.val = 0 by omega), if_neg (show ¬ i.val = 1 by omega), dif_neg h8]

theorem sabs_c3 (salt : Array U32 8#usize) (s : R0P.Digest K) (hs : DigestLift salt s) (clen : Usize)
    (hc : clen.val = 2) :
    ∀ i : Fin 16, noteC3 s i =
      (if i.val < 8 ∧ i.val < clen.val then liftU (K := K) ((noteC3R salt).val[i.val]!) else 0) := by
  intro i
  rw [hc]
  unfold noteC3
  by_cases h2 : i.val < 2
  · rw [if_pos (show i.val < 8 ∧ i.val < 2 from ⟨by omega, h2⟩), noteC3R, arr8_get _ _ (by omega)]
    dsimp only
    by_cases e0 : i.val = 0
    · rw [if_pos e0, if_pos e0]; exact (hs 6).symm
    rw [if_neg e0, if_neg e0, if_pos (show i.val = 1 by omega), if_pos (show i.val = 1 by omega)]
    exact (hs 7).symm
  · rw [if_neg (show ¬ (i.val < 8 ∧ i.val < 2) from fun h => h2 h.2),
      if_neg (show ¬ i.val = 0 by omega), if_neg (show ¬ i.val = 1 by omega)]

/-- The sponge chunk premise, as a named Prop. -/
def SabsOk (pub : R0P.Public K) (w : ModelWitness K) (R : RustChunks) : Prop :=
  ∀ h : Fin 57, ¬ NodeKind h.val → ¬ ZeroKind pub.variant h.val →
    ∀ i : Fin 16, (blocksOf pub w h).absorb i =
      (if i.val < 8 ∧ i.val < (R.sclen h.val).val then liftU (K := K) ((R.schunk h.val).val[i.val]!) else 0)

theorem owner_lift (W : RustWitness) :
    ∃ d, ownerD W = ok d ∧ DigestLift d (ownerDigest (toModel (K := K) W)) ∧ Canon8 d := by
  obtain ⟨p, hp, hpv⟩ := owner_init (K := K) (ownerB (toModel W)) rfl
  obtain ⟨d, hd, hdl, hdc⟩ := spongeDigest_lift p W.sk 8#usize (ownerB (toModel W)) hpv
    (sabs_lo8 W.sk 8#usize n8 _ (fun i => rfl))
  exact ⟨d, by rw [ownerD]; simp only [hp, bind_tc_ok, hd], hdl, hdc⟩

theorem trv (v : R0P.Variant) (h : Nat) (h1 : 27 ≤ h) (h2 : h ≤ 29) (hz : ¬ ZeroKind v h) :
    v = .privateTransfer := by
  cases v
  · rfl
  · exact absurd ⟨rfl, h1, h2⟩ hz

/-- The computed chunks satisfy the chunk premise. -/
theorem chunks_sabs (W : RustWitness) (P : RustPublic) (pub : R0P.Public K) (hP : PubCorr P pub)
    (hW : WitnessOk W) : SabsOk pub (toModel W) (chunksOf W P) := by
  intro h hn hz
  obtain ⟨hv, hh⟩ := h
  dsimp only at hn hz ⊢
  have cases : hv = 0 ∨ hv = 1 ∨ hv = 2 ∨ hv = 3 ∨ hv = 25 ∨ hv = 26 ∨ hv = 27 ∨ hv = 28 ∨ hv = 29 ∨
      hv = 30 ∨ hv = 31 ∨ hv = 32 := by
    unfold NodeKind at hn; omega
  have v0 : liftU (K := K) W.inputValue = ((toModel (K := K) W).inputValue.val : K) := by
    show _ = ((W.inputValue.val % 2 ^ 30 : Nat) : K); rw [Nat.mod_eq_of_lt hW.values.1]; rfl
  have v1 : liftU (K := K) W.outputValue = ((toModel (K := K) W).outputValue.val : K) := by
    show _ = ((W.outputValue.val % 2 ^ 30 : Nat) : K); rw [Nat.mod_eq_of_lt hW.values.2.1]; rfl
  have v2 : liftU (K := K) W.changeValue = ((toModel (K := K) W).changeValue.val : K) := by
    show _ = ((W.changeValue.val % 2 ^ 30 : Nat) : K); rw [Nat.mod_eq_of_lt hW.values.2.2]; rfl
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sabs_lo8 W.sk 8#usize n8 _ (fun i => rfl)
  · obtain ⟨d, hd, hdl, -⟩ := owner_lift (K := K) W
    have e : (chunksOf W P).schunk 1 = d := by show okOr (ownerD W) zero8 = d; rw [hd]; rfl
    rw [e]
    exact sabs_lo8 d 8#usize n8 _ hdl
  · exact sabs_c2 _ _ _ _ _ _ v0 hP.asset (fun i => rfl) 8#usize n8
  · exact sabs_c3 _ _ (fun i => rfl) 2#usize n2
  · exact sabs_lo8 W.sk 8#usize n8 _ (fun i => rfl)
  · exact sabs_lo8 W.salt 8#usize n8 _ (fun i => rfl)
  · have htr := trv pub.variant 27 (by omega) (by omega) hz
    intro i
    show (recipB pub (toModel W) 0).absorb i = _
    unfold recipB; rw [htr]
    exact sabs_lo8 W.recipientOwner 8#usize n8 _ (fun i => rfl) i
  · have htr := trv pub.variant 28 (by omega) (by omega) hz
    intro i
    show (recipB pub (toModel W) 1).absorb i = _
    unfold recipB; rw [htr]
    exact sabs_c2 _ _ _ _ _ _ v1 hP.asset (fun i => rfl) 8#usize n8 i
  · have htr := trv pub.variant 29 (by omega) (by omega) hz
    intro i
    show (recipB pub (toModel W) 2).absorb i = _
    unfold recipB; rw [htr]
    exact sabs_c3 _ _ (fun i => rfl) 2#usize n2 i
  · exact sabs_lo8 W.changeOwner 8#usize n8 _ (fun i => rfl)
  · exact sabs_c2 _ _ _ _ _ _ v2 hP.asset (fun i => rfl) 8#usize n8
  · exact sabs_c3 _ _ (fun i => rfl) 2#usize n2

section chain
variable (pub : R0P.Public K) (w : ModelWitness K) (R : RustChunks) (hS : SabsOk pub w R)

include hS in
theorem spongePre_lift_s (h : Fin 57) (hn : ¬ NodeKind h.val) (hz : ¬ ZeroKind pub.variant h.val) :
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
      (hS ⟨1, by omega⟩ (nk 1 (by omega)) (zk _ 1 (by omega)))
    exact ⟨p2, by simp only [spongePre, hp1, bind_tc_ok, hp2], hv2⟩
  · obtain ⟨p1, hp1, hv1⟩ := s1
    obtain ⟨p2, hp2, hv2⟩ := chain_step _ _ (pre_2 pub w) p1 hv1 (R.schunk 1) (R.sclen 1)
      (hS ⟨1, by omega⟩ (nk 1 (by omega)) (zk _ 1 (by omega)))
    obtain ⟨p3, hp3, hv3⟩ := chain_step _ _ (pre_3 pub w) p2 hv2 (R.schunk 2) (R.sclen 2)
      (hS ⟨2, by omega⟩ (nk 2 (by omega)) (zk _ 2 (by omega)))
    exact ⟨p3, by simp only [spongePre, hp1, bind_tc_ok, hp2, hp3], hv3⟩
  · exact s25
  · obtain ⟨p1, hp1, hv1⟩ := s25
    obtain ⟨p2, hp2, hv2⟩ := chain_step _ _ (pre_26 pub w) p1 hv1 (R.schunk 25) (R.sclen 25)
      (hS ⟨25, by omega⟩ (nk 25 (by omega)) (zk _ 25 (by omega)))
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
      (hS ⟨27, by omega⟩ (nk 27 (by omega)) (zk_tr pub 27 htr))
    exact ⟨p2, by simp only [spongePre, hp1, bind_tc_ok, hp2], hv2⟩
  · have htr : pub.variant = .privateTransfer := by
      cases e : pub.variant
      · rfl
      · exact absurd ⟨e, by omega, by omega⟩ hz
    obtain ⟨p1, hp1, hv1⟩ := note_init (K := K) (blocksOf pub w 27) (by
      show (recipB pub w 0).pre = _; unfold recipB; rw [htr]; rfl)
    obtain ⟨p2, hp2, hv2⟩ := chain_step _ _ (pre_28 pub w htr) p1 hv1 (R.schunk 27) (R.sclen 27)
      (hS ⟨27, by omega⟩ (nk 27 (by omega)) (zk_tr pub 27 htr))
    obtain ⟨p3, hp3, hv3⟩ := chain_step _ _ (pre_29 pub w htr) p2 hv2 (R.schunk 28) (R.sclen 28)
      (hS ⟨28, by omega⟩ (nk 28 (by omega)) (zk_tr pub 28 htr))
    exact ⟨p3, by simp only [spongePre, hp1, bind_tc_ok, hp2, hp3], hv3⟩
  · exact s30
  · obtain ⟨p1, hp1, hv1⟩ := s30
    obtain ⟨p2, hp2, hv2⟩ := chain_step _ _ (pre_31 pub w) p1 hv1 (R.schunk 30) (R.sclen 30)
      (hS ⟨30, by omega⟩ (nk 30 (by omega)) (zk _ 30 (by omega)))
    exact ⟨p2, by simp only [spongePre, hp1, bind_tc_ok, hp2], hv2⟩
  · obtain ⟨p1, hp1, hv1⟩ := s30
    obtain ⟨p2, hp2, hv2⟩ := chain_step _ _ (pre_31 pub w) p1 hv1 (R.schunk 30) (R.sclen 30)
      (hS ⟨30, by omega⟩ (nk 30 (by omega)) (zk _ 30 (by omega)))
    obtain ⟨p3, hp3, hv3⟩ := chain_step _ _ (pre_32 pub w) p2 hv2 (R.schunk 31) (R.sclen 31)
      (hS ⟨31, by omega⟩ (nk 31 (by omega)) (zk _ 31 (by omega)))
    exact ⟨p3, by simp only [spongePre, hp1, bind_tc_ok, hp2, hp3], hv3⟩

end chain

/-! ### Note digests -/

/-- The digest of the last block of a note sponge ending at block h3. -/
def noteDigestR (R : RustChunks) (h3 : Nat) : Result (Array U32 8#usize) := do
  let p ← spongePre R h3
  spongeDigestR p (R.schunk h3) (R.sclen h3)

theorem noteDigest_lift (pub : R0P.Public K) (w : ModelWitness K) (R : RustChunks) (hS : SabsOk pub w R)
    (h : Fin 57) (hn : ¬ NodeKind h.val) (hz : ¬ ZeroKind pub.variant h.val) :
    ∃ d, noteDigestR R h.val = ok d ∧ DigestLift d (blockDigest (blocksOf pub w h)) ∧ Canon8 d := by
  obtain ⟨p, hp, hpv⟩ := spongePre_lift_s pub w R hS h hn hz
  obtain ⟨d, hd, hdl, hdc⟩ := spongeDigest_lift p _ _ _ hpv (hS h hn hz)
  exact ⟨d, by rw [noteDigestR]; simp only [hp, bind_tc_ok, hd], hdl, hdc⟩

#print axioms R0Z.WriterRefine.blockDigest_lift
#print axioms R0Z.WriterRefine.nodeDigest_lift
#print axioms R0Z.WriterRefine.chunks_sabs
#print axioms R0Z.WriterRefine.spongePre_lift_s
#print axioms R0Z.WriterRefine.noteDigest_lift
end R0Z.WriterRefine
