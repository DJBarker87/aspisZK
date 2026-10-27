import R0Z.NoteSpongeModel
import R0Z.BuilderModelCopyMisc

/-! Every writer-produced Poseidon block of the Rust builder equals the
corresponding buildModel block (DESIGN-BUILDER-MODEL §11.0).

`RustWriter v R h` is the copy writer that produces block h (write_node for
the 45 node blocks 4..24, 33..56; write_block of zeros for a withdrawal's
blocks 27..29; write_sponge_block for the sponge blocks).  `builder_blocks_model`:
under `BuilderLifts` — RoundsOk for every block (the Poseidon plug-in), the
node children's lifts, and the sponge pre-states / absorptions' lifts — every
cell of every block equals `buildModel pub w` at row 16h+l.  The discharge
lemmas below reduce the sponge pre-state premise to the Rust sponge chaining
(`spre (h+1) = rounds h [10]`, what production does, covered by the
differential test) and to sponge_init, and instantiate the node/absorption
premises for the tree, append and output-pair nodes and the owner and
nullifier sponges. -/
set_option autoImplicit false
noncomputable section

namespace R0Z.WriterRefine
open Aeneas Aeneas.Std Result
open R0Z.BuilderModel

variable {K : Type} [Field K]

def NodeKind (h : Nat) : Prop := (4 ≤ h ∧ h ≤ 24) ∨ (33 ≤ h ∧ h ≤ 56)
def ZeroKind (v : R0P.Variant) (h : Nat) : Prop := v = .withdrawal ∧ 27 ≤ h ∧ h ≤ 29

instance (h : Nat) : Decidable (NodeKind h) := by unfold NodeKind; infer_instance
instance (v : R0P.Variant) (h : Nat) : Decidable (ZeroKind v h) := by unfold ZeroKind; infer_instance

/-- The Rust inputs of every block (all lifts are premises, see BuilderLifts). -/
structure RustBlocks where
  left : Nat → Array U32 8#usize
  right : Nat → Array U32 8#usize
  spre : Nat → Array U32 16#usize
  schunk : Nat → Array U32 8#usize
  sclen : Nat → Usize
  rounds : Nat → Array (Array U32 16#usize) 11#usize

def zero16 : Array U32 16#usize := Array.repeat 16#usize 0#u32

/-- The copy writer that produces block h. -/
def RustWriter (v : R0P.Variant) (R : RustBlocks) (h : Nat) : Result (Array U32 256#usize) :=
  if NodeKind h then R0BlockCopies.write_node (R.left h) (R.right h) (R.rounds h)
  else if ZeroKind v h then R0BlockCopies.write_block zero16 zero16 (R.rounds h)
  else R0BlockCopies.write_sponge_block (R.spre h) (R.schunk h) (R.sclen h) (R.rounds h)

structure BuilderLifts (pub : R0P.Public K) (w : ModelWitness K) (R : RustBlocks) : Prop where
  rounds : ∀ h : Fin 57, RoundsOk (R.rounds h.val) (blocksOf pub w h)
  node : ∀ h : Fin 57, NodeKind h.val → ∃ L Rr : R0P.Digest K, blocksOf pub w h = nodeIn L Rr ∧
    DigestLift (R.left h.val) L ∧ DigestLift (R.right h.val) Rr ∧
    ∀ i, i < 8 → ((R.right h.val).val[i]!).val < 2147483647
  spre : ∀ h : Fin 57, ¬ NodeKind h.val → ¬ ZeroKind pub.variant h.val →
    ∀ i : Fin 16, liftU (K := K) ((R.spre h.val).val[i.val]!) = (blocksOf pub w h).pre i
  sabs : ∀ h : Fin 57, ¬ NodeKind h.val → ¬ ZeroKind pub.variant h.val →
    ∀ i : Fin 16, (blocksOf pub w h).absorb i =
      (if i.val < 8 ∧ i.val < (R.sclen h.val).val then liftU (K := K) ((R.schunk h.val).val[i.val]!) else 0)

theorem builder_blocks_model [CharP K 0x7fffffff] (pub : R0P.Public K) (w : ModelWitness K) (R : RustBlocks)
    (hL : BuilderLifts pub w R) (h : Fin 57) :
    ∃ b, RustWriter pub.variant R h.val = ok b ∧ ∀ l c : Fin 16,
      liftU (K := K) (b.val[l.val * 16 + c.val]!) =
        buildModel pub w ⟨c.val, by omega⟩ ⟨16 * h.val + l.val, by have := h.isLt; omega⟩ := by
  have cellEq : ∀ (b : Array U32 256#usize),
      (∀ l c : Fin 16, liftU (K := K) (b.val[l.val * 16 + c.val]!) = blockCell (blocksOf pub w h) l.val c) →
      ∀ l c : Fin 16, liftU (K := K) (b.val[l.val * 16 + c.val]!) =
        buildModel pub w ⟨c.val, by omega⟩ ⟨16 * h.val + l.val, by have := h.isLt; omega⟩ := by
    intro b hb l c
    rw [hb l c, buildModel, cell_block _ _ c.isLt h l.val l.isLt _ rfl]
    rfl
  unfold RustWriter
  by_cases hn : NodeKind h.val
  · rw [if_pos hn]
    obtain ⟨L, Rr, he, hl, hr, hc⟩ := hL.node h hn
    obtain ⟨b, hb, hs⟩ := node_model (R.left h.val) (R.right h.val) (R.rounds h.val) L Rr hl hr hc
      (he ▸ hL.rounds h)
    exact ⟨b, hb, cellEq b (by rw [he]; exact hs)⟩
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
    obtain ⟨b, hb, hs⟩ := block_model zero16 zero16 (R.rounds h.val) _ he (hL.rounds h)
    exact ⟨b, hb, cellEq b hs⟩
  · rw [if_neg hz]
    obtain ⟨ab, hab, habs⟩ := sponge_absorb_spec (R.schunk h.val) (R.sclen h.val)
    have he : EndsLift (R.spre h.val) ab (blocksOf pub w h) := by
      refine ⟨hL.spre h hn hz, fun i => ?_⟩
      rw [hL.sabs h hn hz i, habs]
      by_cases c : i.val < 8 ∧ i.val < (R.sclen h.val).val
      · rw [if_pos c, if_pos c]
      · rw [if_neg c, if_neg c]; unfold liftU; simp
    obtain ⟨b, hb, hs⟩ := block_model (R.spre h.val) ab (R.rounds h.val) _ he (hL.rounds h)
    refine ⟨b, ?_, cellEq b hs⟩
    rw [R0BlockCopies.write_sponge_block, hab]
    simp only [bind_tc_ok]
    exact hb

/-! ### Discharging the premises (mechanical instantiations) -/

/-- Sponge chaining: a Rust pre-state equal to the previous block's final
round lifts to the model's pre-state whenever the model chains (pre_2, pre_3,
pre_26, pre_28/29, pre_31, pre_32). -/
theorem spre_chain (pub : R0P.Public K) (w : ModelWitness K) (R : RustBlocks) (h : Fin 57) (h' : Fin 57)
    (hr : RoundsOk (R.rounds h.val) (blocksOf pub w h))
    (hchainR : R.spre h'.val = (R.rounds h.val).val[10]!)
    (hchainM : (blocksOf pub w h').pre = blockOut (blocksOf pub w h)) :
    ∀ i : Fin 16, liftU (K := K) ((R.spre h'.val).val[i.val]!) = (blocksOf pub w h').pre i := by
  intro i
  rw [hchainR, hchainM]
  exact hr 10 i (by norm_num)

/-- First sponge blocks: sponge_init lifts to the model's spongeInit. -/
theorem spre_init (domain len : U32) (dom l : K) (hd : liftU (K := K) domain = dom)
    (hl : liftU (K := K) len = l) (s : Array U32 16#usize)
    (hs : R0BlockCopies.sponge_init domain len = ok s) :
    ∀ i : Fin 16, liftU (K := K) (s.val[i.val]!) = spongeInit dom l i := by
  obtain ⟨s', hs', hv⟩ := sponge_init_spec domain len
  rw [hs] at hs'
  cases hs'
  intro i
  rw [hv]
  unfold spongeInit
  by_cases e8 : i.val = 8
  · rw [if_pos e8, if_pos e8, hd]
  · rw [if_neg e8, if_neg e8]
    by_cases e9 : i.val = 9
    · rw [if_pos e9, if_pos e9, hl]
    · rw [if_neg e9, if_neg e9]; unfold liftU; simp

/-- A full eight-word chunk lifting to a digest gives lo8 absorption. -/
theorem sabs_lo8 (chunk : Array U32 8#usize) (clen : Usize) (hc : clen.val = 8) (D : R0P.Digest K)
    (hD : DigestLift chunk D) :
    ∀ i : Fin 16, lo8 D i = (if i.val < 8 ∧ i.val < clen.val then liftU (K := K) (chunk.val[i.val]!) else 0) := by
  intro i
  unfold lo8
  rw [hc]
  by_cases h8 : i.val < 8
  · rw [dif_pos h8, if_pos ⟨h8, h8⟩]; exact (hD ⟨i.val, h8⟩).symm
  · rw [dif_neg h8, if_neg (fun h => h8 h.1)]

/-- Owner-key sponge (block 0, sk, 8 words). -/
theorem owner_sabs (pub : R0P.Public K) (w : ModelWitness K) (chunk : Array U32 8#usize) (clen : Usize)
    (hc : clen.val = 8) (hD : DigestLift chunk w.sk) :
    ∀ i : Fin 16, (blocksOf pub w 0).absorb i =
      (if i.val < 8 ∧ i.val < clen.val then liftU (K := K) (chunk.val[i.val]!) else 0) :=
  sabs_lo8 chunk clen hc w.sk hD

theorem owner_spre (pub : R0P.Public K) (w : ModelWitness K) (domain len : U32)
    (hd : domain.val = 0x41530001) (hl : len.val = 8) (s : Array U32 16#usize)
    (hs : R0BlockCopies.sponge_init domain len = ok s) :
    ∀ i : Fin 16, liftU (K := K) (s.val[i.val]!) = (blocksOf pub w 0).pre i :=
  spre_init domain len _ _ (by unfold liftU; rw [hd]; norm_num) (by unfold liftU; rw [hl]; norm_num) s hs

/-- Nullifier sponge (blocks 25, 26: sk then salt, 16 words). -/
theorem nul_sabs0 (pub : R0P.Public K) (w : ModelWitness K) (chunk : Array U32 8#usize) (clen : Usize)
    (hc : clen.val = 8) (hD : DigestLift chunk w.sk) :
    ∀ i : Fin 16, (blocksOf pub w 25).absorb i =
      (if i.val < 8 ∧ i.val < clen.val then liftU (K := K) (chunk.val[i.val]!) else 0) :=
  sabs_lo8 chunk clen hc w.sk hD

theorem nul_sabs1 (pub : R0P.Public K) (w : ModelWitness K) (chunk : Array U32 8#usize) (clen : Usize)
    (hc : clen.val = 8) (hD : DigestLift chunk w.salt) :
    ∀ i : Fin 16, (blocksOf pub w 26).absorb i =
      (if i.val < 8 ∧ i.val < clen.val then liftU (K := K) (chunk.val[i.val]!) else 0) :=
  sabs_lo8 chunk clen hc w.salt hD

theorem nul_spre0 (pub : R0P.Public K) (w : ModelWitness K) (domain len : U32)
    (hd : domain.val = 0x41530002) (hl : len.val = 16) (s : Array U32 16#usize)
    (hs : R0BlockCopies.sponge_init domain len = ok s) :
    ∀ i : Fin 16, liftU (K := K) (s.val[i.val]!) = (blocksOf pub w 25).pre i :=
  spre_init domain len _ _ (by unfold liftU; rw [hd]; norm_num) (by unfold liftU; rw [hl]; norm_num) s hs

theorem nul_spre1 (pub : R0P.Public K) (w : ModelWitness K) (R : RustBlocks)
    (hr : RoundsOk (R.rounds 25) (blocksOf pub w 25)) (hchain : R.spre 26 = (R.rounds 25).val[10]!) :
    ∀ i : Fin 16, liftU (K := K) ((R.spre 26).val[i.val]!) = (blocksOf pub w 26).pre i :=
  spre_chain pub w R 25 26 hr hchain (pre_26 pub w)

/-- Tree node blocks: the model's children are the ordered (current, sibling). -/
theorem tree_node_children (pub : R0P.Public K) (w : ModelWitness K) (l : Fin 24) :
    blocksOf pub w ⟨nodeBlock l, nodeBlock_lt l⟩ =
      nodeIn (ordered (treeCur w (inputLeaf pub w) l.val) (w.path l).2 (w.path l).1).1
        (ordered (treeCur w (inputLeaf pub w) l.val) (w.path l).2 (w.path l).1).2 := by
  rw [blocksOf_node']; rfl

/-- Append node blocks 34..53: the model's children are ordered (current, frontier/empty root). -/
theorem app_node_children (pub : R0P.Public K) (w : ModelWitness K) (j : Nat) (hj : j < 20) :
    blocksOf pub w ⟨34 + j, by omega⟩ =
      nodeIn (ordered (appCur pub (outPair pub w) j) (appSib pub ⟨j, hj⟩) (appBit pub j)).1
        (ordered (appCur pub (outPair pub w) j) (appSib pub ⟨j, hj⟩) (appBit pub j)).2 := by
  rw [blocksOf_app' pub w _ j rfl hj]; rfl

/-- The output-pair node (block 33). -/
theorem outpair_children (pub : R0P.Public K) (w : ModelWitness K) :
    blocksOf pub w 33 = (match pub.variant with
      | .privateTransfer => nodeIn (recipientDigest pub w) (changeDigest pub w)
      | .withdrawal => nodeIn (changeDigest pub w) 0) := rfl

/-- The node premise of BuilderLifts for a tree level, from the children's lifts. -/
theorem tree_node_premise (pub : R0P.Public K) (w : ModelWitness K) (R : RustBlocks) (l : Fin 24)
    (hl : DigestLift (R.left (nodeBlock l)) (ordered (treeCur w (inputLeaf pub w) l.val) (w.path l).2 (w.path l).1).1)
    (hr : DigestLift (R.right (nodeBlock l)) (ordered (treeCur w (inputLeaf pub w) l.val) (w.path l).2 (w.path l).1).2)
    (hc : ∀ i, i < 8 → ((R.right (nodeBlock l)).val[i]!).val < 2147483647) :
    ∃ L Rr : R0P.Digest K, blocksOf pub w ⟨nodeBlock l, nodeBlock_lt l⟩ = nodeIn L Rr ∧
      DigestLift (R.left (nodeBlock l)) L ∧ DigestLift (R.right (nodeBlock l)) Rr ∧
      ∀ i, i < 8 → ((R.right (nodeBlock l)).val[i]!).val < 2147483647 :=
  ⟨_, _, tree_node_children pub w l, hl, hr, hc⟩

/-- The node premise for an append level. -/
theorem app_node_premise (pub : R0P.Public K) (w : ModelWitness K) (R : RustBlocks) (j : Nat) (hj : j < 20)
    (hl : DigestLift (R.left (34 + j)) (ordered (appCur pub (outPair pub w) j) (appSib pub ⟨j, hj⟩) (appBit pub j)).1)
    (hr : DigestLift (R.right (34 + j)) (ordered (appCur pub (outPair pub w) j) (appSib pub ⟨j, hj⟩) (appBit pub j)).2)
    (hc : ∀ i, i < 8 → ((R.right (34 + j)).val[i]!).val < 2147483647) :
    ∃ L Rr : R0P.Digest K, blocksOf pub w ⟨34 + j, by omega⟩ = nodeIn L Rr ∧
      DigestLift (R.left (34 + j)) L ∧ DigestLift (R.right (34 + j)) Rr ∧
      ∀ i, i < 8 → ((R.right (34 + j)).val[i]!).val < 2147483647 :=
  ⟨_, _, app_node_children pub w j hj, hl, hr, hc⟩

/-- Rust digests computed as a block's final round lift to the model's digest. -/
theorem digest_from_rounds (rounds : Array (Array U32 16#usize) 11#usize) (B : BlockIn K)
    (hr : RoundsOk rounds B) (d : Array U32 8#usize)
    (hd : ∀ i, i < 8 → d.val[i]! = (rounds.val[10]!).val[i]!) : DigestLift d (blockDigest B) := by
  intro i
  rw [hd i.val i.isLt]
  exact hr 10 (i.castAdd 8) (by norm_num)

#print axioms builder_blocks_model
#print axioms spre_chain
#print axioms spre_init
#print axioms owner_sabs
#print axioms owner_spre
#print axioms nul_sabs0
#print axioms nul_sabs1
#print axioms nul_spre0
#print axioms nul_spre1
#print axioms tree_node_premise
#print axioms app_node_premise
#print axioms outpair_children
#print axioms digest_from_rounds
end R0Z.WriterRefine
