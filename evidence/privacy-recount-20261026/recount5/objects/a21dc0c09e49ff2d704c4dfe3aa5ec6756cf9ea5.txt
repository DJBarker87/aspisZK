import R0Z.BuilderWitness

/-! The witness-level Rust-copy builder, part 2: node children (DESIGN-BUILDER-MODEL §12 (2)).

The running membership digest (levels 0..23, from the input leaf through the
sibling path), the output pair and the running append digest (levels 0..19,
frontier or empty-root sibling by the bits of nextPairIndex) are computed by
the copy's node permutations; `rustChunks W P` is the complete per-block input
(chunks, lengths and node children).  `rust_chunk_lifts`: it satisfies
`BuilderChunkLifts` for `toModel W`, so `builder_witness_blocks`: every block
the chained copy writer produces from (W, P) equals buildModel. -/
set_option autoImplicit false
noncomputable section

namespace R0Z.WriterRefine
open Aeneas Aeneas.Std Result
open R0Z.BuilderModel

def orderedR (cur sib : Array U32 8#usize) (b : Bool) : Array U32 8#usize × Array U32 8#usize :=
  if b then (sib, cur) else (cur, sib)

def bitB (W : RustWitness) (l : Nat) : Bool := decide ((W.bits.val[l]!).val ≠ 0)

def inputLeafR (W : RustWitness) (P : RustPublic) : Result (Array U32 8#usize) := noteDigestR (chunksOf W P) 3
def recipDR (W : RustWitness) (P : RustPublic) : Result (Array U32 8#usize) := noteDigestR (chunksOf W P) 29
def changeDR (W : RustWitness) (P : RustPublic) : Result (Array U32 8#usize) := noteDigestR (chunksOf W P) 32

def treeCurR (W : RustWitness) (P : RustPublic) : Nat → Result (Array U32 8#usize)
  | 0 => inputLeafR W P
  | n + 1 => do
      let c ← treeCurR W P n
      let o := orderedR c (W.sibs.val[n]!) (bitB W n)
      nodeDigestR o.1 o.2

def outPairR (W : RustWitness) (P : RustPublic) : Result (Array U32 8#usize) :=
  match P.variant with
  | .privateTransfer => do
      let r ← recipDR W P
      let c ← changeDR W P
      nodeDigestR r c
  | .withdrawal => do
      let c ← changeDR W P
      nodeDigestR c zero8

def appBitR (P : RustPublic) (n : Nat) : Bool := decide (((P.nextPairIndex >>> n) &&& 1) ≠ 0)

def appSibR (P : RustPublic) (n : Nat) : Array U32 8#usize :=
  if appBitR P n then P.frontier.val[n]! else P.empty.val[n]!

def appCurR (W : RustWitness) (P : RustPublic) : Nat → Result (Array U32 8#usize)
  | 0 => outPairR W P
  | n + 1 => do
      let c ← appCurR W P n
      let o := orderedR c (appSibR P n) (appBitR P n)
      nodeDigestR o.1 o.2

/-- The (left, right) children the builder feeds to node block h. -/
def childrenOf (W : RustWitness) (P : RustPublic) (h : Nat) : Array U32 8#usize × Array U32 8#usize :=
  if 4 ≤ h ∧ h ≤ 24 then orderedR (okOr (treeCurR W P (h - 4)) zero8) (W.sibs.val[h - 4]!) (bitB W (h - 4))
  else if 54 ≤ h then orderedR (okOr (treeCurR W P (h - 33)) zero8) (W.sibs.val[h - 33]!) (bitB W (h - 33))
  else if h = 33 then
    (match P.variant with
      | .privateTransfer => (okOr (recipDR W P) zero8, okOr (changeDR W P) zero8)
      | .withdrawal => (okOr (changeDR W P) zero8, zero8))
  else if 34 ≤ h ∧ h ≤ 53 then
    orderedR (okOr (appCurR W P (h - 34)) zero8) (appSibR P (h - 34)) (appBitR P (h - 34))
  else (zero8, zero8)

/-- **The complete per-block Rust input computed from the records.** -/
def rustChunks (W : RustWitness) (P : RustPublic) : RustChunks :=
  { chunksOf W P with left := fun h => (childrenOf W P h).1, right := fun h => (childrenOf W P h).2 }

variable {K : Type} [Field K]

theorem ordered_lift (c s : Array U32 8#usize) (C S : R0P.Digest K) (b : Bool)
    (hc : DigestLift c C) (hs : DigestLift s S) (hcc : Canon8 c) (hsc : Canon8 s) :
    DigestLift (orderedR c s b).1 (ordered C S b).1 ∧ DigestLift (orderedR c s b).2 (ordered C S b).2 ∧
      Canon8 (orderedR c s b).2 := by
  cases b
  · exact ⟨hc, hs, hsc⟩
  · exact ⟨hs, hc, hcc⟩

theorem zero8_lift : DigestLift (K := K) zero8 0 := by
  intro i
  show liftU ((arr8 (fun _ => 0#u32)).val[i.val]!) = 0
  rw [arr8_get _ _ i.isLt]
  unfold liftU; simp

theorem zero8_canon : Canon8 zero8 := by
  intro i hi
  show ((arr8 (fun _ => 0#u32)).val[i]!).val < _
  rw [arr8_get _ _ hi]; simp

theorem treeCur_succ (w : ModelWitness K) (leaf : R0P.Digest K) (n : Nat) (hn : n < 24) :
    treeCur w leaf (n + 1) = blockDigest (treeNode w (treeCur w leaf n) ⟨n, hn⟩) := by
  first
  | exact dif_pos hn
  | simp only [treeCur, dif_pos hn]

theorem appCur_succ (pub : R0P.Public K) (start : R0P.Digest K) (n : Nat) (hn : n < 20) :
    appCur pub start (n + 1) = blockDigest (appNode pub (appCur pub start n) ⟨n, hn⟩) := by
  first
  | exact dif_pos hn
  | simp only [appCur, dif_pos hn]

variable [CharP K 0x7fffffff]

section build
variable (W : RustWitness) (P : RustPublic) (pub : R0P.Public K) (hP : PubCorr P pub) (hW : WitnessOk W)

include hP hW in
theorem treeCur_lift : ∀ l, l ≤ 24 → ∃ c, treeCurR W P l = ok c ∧
    DigestLift c (treeCur (toModel W) (inputLeaf pub (toModel W)) l) ∧ Canon8 c
  | 0, _ => by
      obtain ⟨d, hd, hdl, hdc⟩ := noteDigest_lift pub (toModel (K := K) W) (chunksOf W P)
        (chunks_sabs W P pub hP hW) 3 (nk 3 (by omega)) (zk _ 3 (by omega))
      exact ⟨d, hd, hdl, hdc⟩
  | n + 1, hn => by
      obtain ⟨c, hc, hcl, hcc⟩ := treeCur_lift n (by omega)
      have ol := ordered_lift c (W.sibs.val[n]!) _ (digK (K := K) (W.sibs.val[n]!)) (bitB W n) hcl
        (fun i => rfl) hcc (hW.sibs n (by omega))
      obtain ⟨d, hd, hdl, hdc⟩ := nodeDigest_lift _ _ _ _ ol.1 ol.2.1 ol.2.2
      refine ⟨d, ?_, ?_, hdc⟩
      · show (do let c ← treeCurR W P n; let o := orderedR c (W.sibs.val[n]!) (bitB W n); nodeDigestR o.1 o.2) = _
        rw [hc]
        simp only [bind_tc_ok]
        exact hd
      · rw [treeCur_succ _ _ n (by omega)]
        exact hdl

include hP hW in
theorem outPair_lift : ∃ c, outPairR W P = ok c ∧ DigestLift c (outPair pub (toModel W)) ∧ Canon8 c := by
  obtain ⟨dc, hdc, hdcl, hdcc⟩ := noteDigest_lift pub (toModel (K := K) W) (chunksOf W P)
    (chunks_sabs W P pub hP hW) 32 (nk 32 (by omega)) (zk _ 32 (by omega))
  replace hdc : noteDigestR (chunksOf W P) 32 = ok dc := hdc
  unfold outPairR outPair outPairB
  rw [hP.variant]
  cases hv : pub.variant
  · have hz : ¬ ZeroKind pub.variant 29 := zk_tr pub 29 hv
    obtain ⟨dr, hdr, hdrl, hdrc⟩ := noteDigest_lift pub (toModel (K := K) W) (chunksOf W P)
      (chunks_sabs W P pub hP hW) 29 (nk 29 (by omega)) hz
    replace hdr : noteDigestR (chunksOf W P) 29 = ok dr := hdr
    obtain ⟨d, hd, hdl, hdd⟩ := nodeDigest_lift dr dc _ _ hdrl hdcl hdcc
    refine ⟨d, ?_, hdl, hdd⟩
    show (do let r ← noteDigestR (chunksOf W P) 29; let c ← noteDigestR (chunksOf W P) 32; nodeDigestR r c) = _
    rw [hdr, hdc]
    simp only [bind_tc_ok]
    exact hd
  · obtain ⟨d, hd, hdl, hdd⟩ := nodeDigest_lift dc zero8 _ _ hdcl zero8_lift zero8_canon
    refine ⟨d, ?_, hdl, hdd⟩
    show (do let c ← noteDigestR (chunksOf W P) 32; nodeDigestR c zero8) = _
    rw [hdc]
    simp only [bind_tc_ok]
    exact hd

include hP in
theorem appBit_eq (n : Nat) : appBitR P n = appBit pub n := by
  unfold appBitR appBit
  rw [hP.next]

include hP in
theorem appSib_lift (n : Nat) (hn : n < 20) :
    DigestLift (appSibR P n) (appSib pub ⟨n, hn⟩) ∧ Canon8 (appSibR P n) := by
  unfold appSibR appSib
  rw [appBit_eq P pub hP n]
  by_cases hb : appBit pub n = true
  · rw [if_pos hb, if_pos hb]
    exact ⟨hP.frontier ⟨n, hn⟩, hP.frontierCanon ⟨n, hn⟩⟩
  · rw [if_neg hb, if_neg hb]
    exact ⟨hP.empty ⟨n, hn⟩, hP.emptyCanon ⟨n, hn⟩⟩

include hP hW in
theorem appCur_lift : ∀ j, j ≤ 20 → ∃ c, appCurR W P j = ok c ∧
    DigestLift c (appCur pub (outPair pub (toModel W)) j) ∧ Canon8 c
  | 0, _ => outPair_lift W P pub hP hW
  | n + 1, hn => by
      obtain ⟨c, hc, hcl, hcc⟩ := appCur_lift n (by omega)
      have hs := appSib_lift P pub hP n (by omega)
      have ol := ordered_lift c (appSibR P n) _ _ (appBitR P n) hcl hs.1 hcc hs.2
      obtain ⟨d, hd, hdl, hdc⟩ := nodeDigest_lift _ _ _ _ ol.1 ol.2.1 ol.2.2
      refine ⟨d, ?_, ?_, hdc⟩
      · show (do let c ← appCurR W P n; let o := orderedR c (appSibR P n) (appBitR P n); nodeDigestR o.1 o.2) = _
        rw [hc]
        simp only [bind_tc_ok]
        exact hd
      · rw [appCur_succ _ _ n (by omega)]
        unfold appNode
        rw [← appBit_eq P pub hP n]
        exact hdl

include hP hW in
/-- The computed node children satisfy the node premise. -/
theorem rust_node_lifts (h : Fin 57) (hn : NodeKind h.val) :
    ∃ L Rr : R0P.Digest K, blocksOf pub (toModel W) h = nodeIn L Rr ∧
      DigestLift ((rustChunks W P).left h.val) L ∧ DigestLift ((rustChunks W P).right h.val) Rr ∧
      ∀ i, i < 8 → (((rustChunks W P).right h.val).val[i]!).val < 2147483647 := by
  have h57 := h.isLt
  unfold NodeKind at hn
  by_cases h24 : h.val ≤ 24
  · have e : childrenOf W P h.val = orderedR (okOr (treeCurR W P (h.val - 4)) zero8)
        (W.sibs.val[h.val - 4]!) (bitB W (h.val - 4)) := by
      unfold childrenOf; rw [if_pos ⟨by omega, h24⟩]
    obtain ⟨c, hc, hcl, hcc⟩ := treeCur_lift W P pub hP hW (h.val - 4) (by omega)
    rw [hc, okOr_ok] at e
    have ol := ordered_lift c (W.sibs.val[h.val - 4]!) _ (digK (K := K) (W.sibs.val[h.val - 4]!))
      (bitB W (h.val - 4)) hcl (fun i => rfl) hcc (hW.sibs _ (by omega))
    refine ⟨_, _, blocksOf_tree_lo pub (toModel W) h (by omega) h24, ?_, ?_, ?_⟩
    · show DigestLift (childrenOf W P h.val).1 _; rw [e]; exact ol.1
    · show DigestLift (childrenOf W P h.val).2 _; rw [e]; exact ol.2.1
    · show ∀ i, i < 8 → (((childrenOf W P h.val).2).val[i]!).val < _; rw [e]; exact ol.2.2
  by_cases h54 : 54 ≤ h.val
  · have e : childrenOf W P h.val = orderedR (okOr (treeCurR W P (h.val - 33)) zero8)
        (W.sibs.val[h.val - 33]!) (bitB W (h.val - 33)) := by
      unfold childrenOf; rw [if_neg (by omega), if_pos h54]
    obtain ⟨c, hc, hcl, hcc⟩ := treeCur_lift W P pub hP hW (h.val - 33) (by omega)
    rw [hc, okOr_ok] at e
    have ol := ordered_lift c (W.sibs.val[h.val - 33]!) _ (digK (K := K) (W.sibs.val[h.val - 33]!))
      (bitB W (h.val - 33)) hcl (fun i => rfl) hcc (hW.sibs _ (by omega))
    refine ⟨_, _, blocksOf_tree_hi pub (toModel W) h h54, ?_, ?_, ?_⟩
    · show DigestLift (childrenOf W P h.val).1 _; rw [e]; exact ol.1
    · show DigestLift (childrenOf W P h.val).2 _; rw [e]; exact ol.2.1
    · show ∀ i, i < 8 → (((childrenOf W P h.val).2).val[i]!).val < _; rw [e]; exact ol.2.2
  by_cases h33 : h.val = 33
  · have hb : blocksOf pub (toModel (K := K) W) h = outPairB pub (toModel W) := by
      have : h = 33 := Fin.ext h33
      rw [this]; rfl
    have e : childrenOf W P h.val = (match P.variant with
        | .privateTransfer => (okOr (recipDR W P) zero8, okOr (changeDR W P) zero8)
        | .withdrawal => (okOr (changeDR W P) zero8, zero8)) := by
      unfold childrenOf; rw [if_neg (by omega), if_neg (by omega), if_pos h33]
    obtain ⟨dc, hdc, hdcl, hdcc⟩ := noteDigest_lift pub (toModel (K := K) W) (chunksOf W P)
      (chunks_sabs W P pub hP hW) 32 (nk 32 (by omega)) (zk _ 32 (by omega))
    replace hdc : noteDigestR (chunksOf W P) 32 = ok dc := hdc
    rw [hb]
    unfold outPairB
    rw [hP.variant] at e
    cases hv : pub.variant
    · rw [hv] at e
      obtain ⟨dr, hdr, hdrl, hdrc⟩ := noteDigest_lift pub (toModel (K := K) W) (chunksOf W P)
        (chunks_sabs W P pub hP hW) 29 (nk 29 (by omega)) (zk_tr pub 29 hv)
      replace hdr : noteDigestR (chunksOf W P) 29 = ok dr := hdr
      have e2 : childrenOf W P h.val = (dr, dc) := by
        rw [e]; show (okOr (noteDigestR (chunksOf W P) 29) zero8, okOr (noteDigestR (chunksOf W P) 32) zero8) = _
        rw [hdr, hdc]; rfl
      refine ⟨_, _, rfl, ?_, ?_, ?_⟩
      · show DigestLift (childrenOf W P h.val).1 _; rw [e2]; exact hdrl
      · show DigestLift (childrenOf W P h.val).2 _; rw [e2]; exact hdcl
      · show ∀ i, i < 8 → (((childrenOf W P h.val).2).val[i]!).val < _; rw [e2]; exact hdcc
    · rw [hv] at e
      have e2 : childrenOf W P h.val = (dc, zero8) := by
        rw [e]; show (okOr (noteDigestR (chunksOf W P) 32) zero8, zero8) = _
        rw [hdc]; rfl
      refine ⟨_, _, rfl, ?_, ?_, ?_⟩
      · show DigestLift (childrenOf W P h.val).1 _; rw [e2]; exact hdcl
      · show DigestLift (childrenOf W P h.val).2 _; rw [e2]; exact zero8_lift
      · show ∀ i, i < 8 → (((childrenOf W P h.val).2).val[i]!).val < _; rw [e2]; exact zero8_canon
  · have h34 : 34 ≤ h.val := by omega
    have h53 : h.val ≤ 53 := by omega
    have e : childrenOf W P h.val = orderedR (okOr (appCurR W P (h.val - 34)) zero8)
        (appSibR P (h.val - 34)) (appBitR P (h.val - 34)) := by
      unfold childrenOf; rw [if_neg (by omega), if_neg (by omega), if_neg h33, if_pos ⟨h34, h53⟩]
    obtain ⟨c, hc, hcl, hcc⟩ := appCur_lift W P pub hP hW (h.val - 34) (by omega)
    rw [hc, okOr_ok] at e
    have hs := appSib_lift P pub hP (h.val - 34) (by omega)
    have ol := ordered_lift c (appSibR P (h.val - 34)) _ _ (appBitR P (h.val - 34)) hcl hs.1 hcc hs.2
    rw [appBit_eq P pub hP] at ol
    refine ⟨_, _, blocksOf_app pub (toModel W) h h34 h53, ?_, ?_, ?_⟩
    · show DigestLift (childrenOf W P h.val).1 _; rw [e, appBit_eq P pub hP]; exact ol.1
    · show DigestLift (childrenOf W P h.val).2 _; rw [e, appBit_eq P pub hP]; exact ol.2.1
    · show ∀ i, i < 8 → (((childrenOf W P h.val).2).val[i]!).val < _
      rw [e, appBit_eq P pub hP]; exact ol.2.2

include hP hW in
theorem rust_chunk_lifts : BuilderChunkLifts pub (toModel W) (rustChunks W P) :=
  ⟨rust_node_lifts W P pub hP hW, chunks_sabs W P pub hP hW⟩

include hP hW in
/-- **All 57 blocks from the records.** -/
theorem builder_witness_blocks (h : Fin 57) :
    ∃ b, RustWriterChain P.variant (rustChunks W P) h.val = ok b ∧ ∀ l c : Fin 16,
      liftU (K := K) (b.val[l.val * 16 + c.val]!) =
        buildModel pub (toModel W) ⟨c.val, by omega⟩ ⟨16 * h.val + l.val, by have := h.isLt; omega⟩ := by
  rw [hP.variant]
  exact builder_blocks_model_chain pub (toModel W) (rustChunks W P) (rust_chunk_lifts W P pub hP hW) h

end build

#print axioms R0Z.WriterRefine.treeCur_lift
#print axioms R0Z.WriterRefine.appCur_lift
#print axioms R0Z.WriterRefine.rust_node_lifts
#print axioms R0Z.WriterRefine.builder_witness_blocks
end R0Z.WriterRefine
