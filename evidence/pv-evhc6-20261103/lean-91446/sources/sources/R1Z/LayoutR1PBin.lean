import R1Z.GamesR1PBin

/-! BINARY format (LOG D76; crates/aspis-r1-cost-probe/src/multiproof.rs
`binary_parent`: node `0x12 ‖ left ‖ right`, eighteen levels, leaves unchanged).
The eight-way original is `R1Z.LayoutR1P`, unchanged; here only the node
index algebra (`child_bound*`, `childQ`, `rootChild`), `nodeBytes` and the
designated child of a node (the right child, `1`) differ.

The commitment-phase byte layout of R1 (DESIGN-R1-REAL §3), from the Rust
source (read with `git show origin/codex/100bit-spend-path-20261013:…`):
prover.rs (precommit binding, three salted trees), state_only_entropy.rs
(attempt binding, source / D seeds, leaf salts, Profile21 expander),
state_only_hiding.rs (mask seed, SeedExpander), aspis-core state_only_hiding.rs
(`StateOnlyHidingContext::encode`), multiproof.rs (binary node `0x12 ‖ 2
children`), state_only_private_merkle.rs (leaf `0x10 ‖ tag ‖ value ‖ salt`).
Every Rust hash is `SHA256` of the concatenation of its slices.

* `gram`: the address of every commitment read (named premise
  `RCommitBytes Pr`: `Pr.caddr` is `gram`).
* `src`: the DESIGNATED FIELD of each read — an attempt secret (nonce,
  entropy, leaf-salt seed) or the answer of an earlier `RIdx` read — and
  `fld`: its reader (trailing 32 bytes, or a fixed offset).  `fld_gram`.
* `depS`: which secrets / `RIdx` answers each address reads; `gram` is
  unchanged by every other coordinate (`gram_rest_update`, `gram_sec_update`).
* `fresh_or_sep`: for two distinct reads, one does not read the other's
  designated field, or (seeds 0/1, two salts, two blocks of one expander
  stream) their addresses differ for every input.
* `openedQ`: the opened reads (roots, leaves at the opened fibres and their
  ancestors); `hidden`: the designated field of an unopened read is neither
  read by nor the answer of any opened read. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.LayoutR1PBin
open R0Z.FsStatement R1Z.LensR1 R1Z.TranscriptR1 R1Z.GamesR1PBin

/-! ### Byte constants -/

/-- "UNPROVED:R1:P3:PRIVATE-ATTEMPT" (prover.rs prove_masked_attempt binding), 30 bytes. -/
def dBind0 : List UInt8 := [85, 78, 80, 82, 79, 86, 69, 68, 58, 82, 49, 58, 80, 51, 58, 80, 82, 73, 86, 65, 84, 69, 45, 65, 84, 84, 69, 77, 80, 84]

/-- "aspis:state-only:pool-v1:private-attempt-binding:v1" (state_only_entropy.rs POOL_V1_PRIVATE_ATTEMPT_BINDING_DOMAIN), 51 bytes. -/
def dBind1 : List UInt8 := [97, 115, 112, 105, 115, 58, 115, 116, 97, 116, 101, 45, 111, 110, 108, 121, 58, 112, 111, 111, 108, 45, 118, 49, 58, 112, 114, 105, 118, 97, 116, 101, 45, 97, 116, 116, 101, 109, 112, 116, 45, 98, 105, 110, 100, 105, 110, 103, 58, 118, 49]

/-- "profile=pool-v1-tag73;generators=H26,G27,D28;factorD=0;rows=1024;c1=16;selected=28;theta=29;queries=16;first-cap=203" (state_only_entropy.rs POOL_V1_PRIVATE_WIRE_DESCRIPTOR), 116 bytes. -/
def descr : List UInt8 := [112, 114, 111, 102, 105, 108, 101, 61, 112, 111, 111, 108, 45, 118, 49, 45, 116, 97, 103, 55, 51, 59, 103, 101, 110, 101, 114, 97, 116, 111, 114, 115, 61, 72, 50, 54, 44, 71, 50, 55, 44, 68, 50, 56, 59, 102, 97, 99, 116, 111, 114, 68, 61, 48, 59, 114, 111, 119, 115, 61, 49, 48, 50, 52, 59, 99, 49, 61, 49, 54, 59, 115, 101, 108, 101, 99, 116, 101, 100, 61, 50, 56, 59, 116, 104, 101, 116, 97, 61, 50, 57, 59, 113, 117, 101, 114, 105, 101, 115, 61, 49, 54, 59, 102, 105, 114, 115, 116, 45, 99, 97, 112, 61, 50, 48, 51]

/-- "aspis:state-only:private-mask-seed:v1" (state_only_hiding.rs MASK_SEED_DOMAIN), 37 bytes. -/
def dMaskSeed : List UInt8 := [97, 115, 112, 105, 115, 58, 115, 116, 97, 116, 101, 45, 111, 110, 108, 121, 58, 112, 114, 105, 118, 97, 116, 101, 45, 109, 97, 115, 107, 45, 115, 101, 101, 100, 58, 118, 49]

/-- "aspis:state-only:pool-v1:source-seed:v1" (state_only_entropy.rs POOL_V1_SOURCE_SEED_DOMAIN), 39 bytes. -/
def dSourceSeed : List UInt8 := [97, 115, 112, 105, 115, 58, 115, 116, 97, 116, 101, 45, 111, 110, 108, 121, 58, 112, 111, 111, 108, 45, 118, 49, 58, 115, 111, 117, 114, 99, 101, 45, 115, 101, 101, 100, 58, 118, 49]

/-- "aspis:state-only:pool-v1:zero-factor-d-seed:v1" (state_only_entropy.rs POOL_V1_D_SEED_DOMAIN), 46 bytes. -/
def dDSeed : List UInt8 := [97, 115, 112, 105, 115, 58, 115, 116, 97, 116, 101, 45, 111, 110, 108, 121, 58, 112, 111, 111, 108, 45, 118, 49, 58, 122, 101, 114, 111, 45, 102, 97, 99, 116, 111, 114, 45, 100, 45, 115, 101, 101, 100, 58, 118, 49]

/-- "aspis:state-only:private-leaf-salt:v1" (state_only_entropy.rs LEAF_SALT_DOMAIN), 37 bytes. -/
def dLeafSalt : List UInt8 := [97, 115, 112, 105, 115, 58, 115, 116, 97, 116, 101, 45, 111, 110, 108, 121, 58, 112, 114, 105, 118, 97, 116, 101, 45, 108, 101, 97, 102, 45, 115, 97, 108, 116, 58, 118, 49]

/-- "aspis:state-only:private-mask-expand:v1" (state_only_hiding.rs MASK_EXPAND_DOMAIN), 39 bytes. -/
def dExp1 : List UInt8 := [97, 115, 112, 105, 115, 58, 115, 116, 97, 116, 101, 45, 111, 110, 108, 121, 58, 112, 114, 105, 118, 97, 116, 101, 45, 109, 97, 115, 107, 45, 101, 120, 112, 97, 110, 100, 58, 118, 49]

/-- "aspis:state-only:profile21:source-expand:v1" (state_only_entropy.rs PROFILE21_SOURCE_EXPAND_DOMAIN), 43 bytes. -/
def dExp2 : List UInt8 := [97, 115, 112, 105, 115, 58, 115, 116, 97, 116, 101, 45, 111, 110, 108, 121, 58, 112, 114, 111, 102, 105, 108, 101, 50, 49, 58, 115, 111, 117, 114, 99, 101, 45, 101, 120, 112, 97, 110, 100, 58, 118, 49]
/-- Little-endian u64 (Rust `u64::to_le_bytes`). -/
def le64 (n : ℕ) : List UInt8 :=
  [(n % 256).toUInt8, (n / 256 % 256).toUInt8, (n / 65536 % 256).toUInt8,
    (n / 16777216 % 256).toUInt8, (n / 4294967296 % 256).toUInt8,
    (n / 1099511627776 % 256).toUInt8, (n / 281474976710656 % 256).toUInt8,
    (n / 72057594037927936 % 256).toUInt8]

/-- PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1. -/
def fpMask : ℕ := 0xf9daf3d54f4285d1
/-- PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1. -/
def fpFactor : ℕ := 0x698bcdedff44a4db

/-- `StateOnlyHidingContext::encode` (81 bytes): version 1, statement digest,
mask nonce, the two fingerprints. -/
def ctxEnc (d nonce : OracleAnswer) : List UInt8 :=
  [1] ++ ans d ++ ans nonce ++ le64 fpMask ++ le64 fpFactor

/-- Tree tags: C1 `0x71`, C2 `0xf1` (r0/merkle.rs), folded `0x72` (prover.rs). -/
def treeTag (T : Fin 3) : UInt8 := if T.val = 0 then 0x71 else if T.val = 1 then 0xf1 else 0x72

/-! ### Index helpers -/

def qBind (b : Fin 2) : RIdx := .inl b
def qSeed (i : Fin 3) : RIdx := .inr (.inl i)
def qSalt (T : Fin 3) (u : Fib) : RIdx := .inr (.inr (.inl (T, u)))
def qLeaf (T : Fin 3) (u : Fib) : RIdx := .inr (.inr (.inr (.inl (T, u))))
def qNode (T : Fin 3) (n : NodeIdx) : RIdx := .inr (.inr (.inr (.inr (T, n))))

theorem child_bound0 (i : Fin (2 ^ (17 - 0))) (j : Fin 2) : 2 * i.val + j.val < 2 ^ 18 := by
  have hi : i.val < 131072 := by simpa using i.isLt
  have hj := j.isLt
  have : (2 : ℕ) ^ 18 = 262144 := by norm_num
  omega

theorem child_bound (d : ℕ) (hd : d + 1 < 17) (i : Fin (2 ^ (17 - (d + 1)))) (j : Fin 2) :
    2 * i.val + j.val < 2 ^ (17 - d) := by
  have hi := i.isLt
  have hj := j.isLt
  rw [show 17 - d = (17 - (d + 1)) + 1 by omega, pow_succ]
  generalize 2 ^ (17 - (d + 1)) = X at *
  omega

/-- The `j`-th child of a non-root node: a leaf (level 1) or a node one level down. -/
def childQ (T : Fin 3) : NodeIdx → Fin 2 → RIdx
  | ⟨⟨0, _⟩, i⟩, j => qLeaf T ⟨2 * i.val + j.val, child_bound0 i j⟩
  | ⟨⟨d + 1, hd⟩, i⟩, j => qNode T ⟨⟨d, by omega⟩, ⟨2 * i.val + j.val, child_bound d hd i j⟩⟩

/-- The `j`-th child of the root of tree `T`: level-17 node `j`. -/
def rootChild (T : Fin 3) (j : Fin 2) : RIdx :=
  qNode T ⟨⟨16, by norm_num⟩, ⟨j.val, lt_of_lt_of_eq j.isLt (by norm_num)⟩⟩

/-- The binary node tag (multiproof.rs `BINARY_NODE_TAG`). -/
def binTag : UInt8 := 0x12

/-- `0x12 ‖ left ‖ right` (multiproof.rs `binary_parent`). -/
def nodeBytes (rest : RIdx → OracleAnswer) (ch : Fin 2 → RIdx) : List UInt8 :=
  [binTag] ++ ans (rest (ch 0)) ++ ans (rest (ch 1))

/-! ### The address grammar -/

section Gram
variable {E₁ E₂ : ℕ}

/-- The Rust address of every commitment read of one attempt. -/
def gram (pub : List UInt8) (vtag : UInt8) (lv : Fin 3 → Fib → List UInt8) (sec : SecP)
    (d : OracleAnswer) (rest : RIdx → OracleAnswer) : CPos E₁ E₂ → List UInt8
  | .inl T => nodeBytes rest (rootChild T)
  | .inr (.inl (.inl c)) => dExp1 ++ ans (rest (qSeed 0)) ++ le64 c.val
  | .inr (.inl (.inr c)) => dExp2 ++ ans (rest (qSeed 2)) ++ le64 c.val
  | .inr (.inr (.inl b)) =>
      if b.val = 0 then dBind0 ++ pub ++ [vtag] ++ ctxEnc d (sec 0).1
      else dBind1 ++ ans (rest (qBind 0)) ++ ctxEnc d (sec 0).1 ++ descr
  | .inr (.inr (.inr (.inl i))) =>
      if i.val = 0 then dMaskSeed ++ ans (rest (qBind 0)) ++ ctxEnc d (sec 0).1 ++ ans (sec 1).1
      else if i.val = 1 then dSourceSeed ++ ans (rest (qBind 0)) ++ ctxEnc d (sec 0).1 ++ ans (sec 1).1
      else dDSeed ++ ans (rest (qBind 1)) ++ ans (rest (qSeed 1))
  | .inr (.inr (.inr (.inr (.inl (T, u))))) =>
      dLeafSalt ++ ans (rest (qBind 1)) ++ ans (sec 0).1 ++ [treeTag T] ++ le32 u.val ++ ans (sec 2).1
  | .inr (.inr (.inr (.inr (.inr (.inl (T, u)))))) =>
      [0x10, treeTag T] ++ lv T u ++ ans (rest (qSalt T u))
  | .inr (.inr (.inr (.inr (.inr (.inr (T, n)))))) => nodeBytes rest (childQ T n)

/-- Designated-field coordinates: an attempt secret slot or an `RIdx` answer. -/
abbrev Src := Fin 3 ⊕ RIdx

def src : CPos E₁ E₂ → Src
  | .inl T => .inr (rootChild T 1)
  | .inr (.inl (.inl _)) => .inr (qSeed 0)
  | .inr (.inl (.inr _)) => .inr (qSeed 2)
  | .inr (.inr (.inl b)) => if b.val = 0 then .inl 0 else .inr (qBind 0)
  | .inr (.inr (.inr (.inl i))) => if i.val = 2 then .inr (qSeed 1) else .inl 1
  | .inr (.inr (.inr (.inr (.inl _)))) => .inl 2
  | .inr (.inr (.inr (.inr (.inr (.inl (T, u)))))) => .inr (qSalt T u)
  | .inr (.inr (.inr (.inr (.inr (.inr (T, n)))))) => .inr (childQ T n 1)

/-- The secrets / `RIdx` answers an address reads (the tape, the challenges
and the leaf values are read by leaves only and are not designated fields). -/
def depS : CPos E₁ E₂ → Src → Prop
  | .inl T, s => ∃ j, s = .inr (rootChild T j)
  | .inr (.inl (.inl _)), s => s = .inr (qSeed 0)
  | .inr (.inl (.inr _)), s => s = .inr (qSeed 2)
  | .inr (.inr (.inl b)), s => if b.val = 0 then s = .inl 0 else (s = .inl 0 ∨ s = .inr (qBind 0))
  | .inr (.inr (.inr (.inl i))), s =>
      if i.val = 2 then (s = .inr (qBind 1) ∨ s = .inr (qSeed 1))
      else (s = .inl 0 ∨ s = .inl 1 ∨ s = .inr (qBind 0))
  | .inr (.inr (.inr (.inr (.inl _)))), s => s = .inl 0 ∨ s = .inl 2 ∨ s = .inr (qBind 1)
  | .inr (.inr (.inr (.inr (.inr (.inl (T, u)))))), s => s = .inr (qSalt T u)
  | .inr (.inr (.inr (.inr (.inr (.inr (T, n)))))), s => ∃ j, s = .inr (childQ T n j)

/-- The value of a designated-field coordinate. -/
def srcVal (sec : SecP) (rest : RIdx → OracleAnswer) : Src → OracleAnswer
  | .inl i => (sec i).1
  | .inr q => rest q

/-- The 32 bytes at offset `n`. -/
def slice (n : ℕ) (a : List UInt8) : OracleAnswer := fun i => a.getD (n + i.val) 0

/-- The designated-field reader of each read (`publen` = |public bytes|). -/
def fld (publen : ℕ) : CPos E₁ E₂ → List UInt8 → OracleAnswer
  | .inr (.inl (.inl _)) => slice dExp1.length
  | .inr (.inl (.inr _)) => slice dExp2.length
  | .inr (.inr (.inl b)) => if b.val = 0 then slice (dBind0.length + publen + 1 + 1 + 32) else slice dBind1.length
  | _ => trailing


/-! ### Designated fields -/

theorem slice_mid (p : List UInt8) (u : OracleAnswer) (q : List UInt8) :
    slice p.length (p ++ ans u ++ q) = u := by
  funext i
  have h1 : p.length + i.val < (p ++ ans u).length := by
    simp only [List.length_append, length_ans]
    omega
  simp only [slice, List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  exact getD_ans u i

theorem fld_gram (pub : List UInt8) (vtag : UInt8) (lv : Fin 3 → Fib → List UInt8) (sec : SecP)
    (d : OracleAnswer) (rest : RIdx → OracleAnswer) (c : CPos E₁ E₂) :
    fld pub.length c (gram pub vtag lv sec d rest c) = srcVal sec rest (src c) := by
  rcases c with T | (c | c) | (b | i | ⟨T, u⟩ | ⟨T, u⟩ | ⟨T, n⟩)
  · exact trailing_append_ans _ _
  · exact slice_mid _ _ _
  · exact slice_mid _ _ _
  · by_cases hb : b.val = 0
    · simp only [fld, gram, src, hb, if_true, srcVal]
      have e : dBind0 ++ pub ++ [vtag] ++ ctxEnc d (sec 0).1 =
          (dBind0 ++ pub ++ [vtag] ++ [1] ++ ans d) ++ ans (sec 0).1 ++ (le64 fpMask ++ le64 fpFactor) := by
        simp only [ctxEnc, List.append_assoc]
      have hl : dBind0.length + pub.length + 1 + 1 + 32 = (dBind0 ++ pub ++ [vtag] ++ [1] ++ ans d).length := by
        simp only [List.length_append, length_ans, List.length_singleton]
      rw [e, hl]
      exact slice_mid _ _ _
    · simp only [fld, gram, src, hb, if_false, srcVal]
      have e : dBind1 ++ ans (rest (qBind 0)) ++ ctxEnc d (sec 0).1 ++ descr =
          dBind1 ++ ans (rest (qBind 0)) ++ (ctxEnc d (sec 0).1 ++ descr) := by
        simp only [List.append_assoc]
      rw [e]
      exact slice_mid _ _ _
  · by_cases h0 : i.val = 0
    · simp only [fld, gram, src, h0, if_true, srcVal, show ¬ (0 = 2) from by decide, if_false]
      exact trailing_append_ans _ _
    · by_cases h1 : i.val = 1
      · simp only [fld, gram, src, h0, h1, if_true, if_false, srcVal, show ¬ (1 = 2) from by decide]
        exact trailing_append_ans _ _
      · have h2 : i.val = 2 := by omega
        simp only [fld, gram, src, h0, h1, h2, if_true, if_false, srcVal]
        exact trailing_append_ans _ _
  · exact trailing_append_ans _ _
  · exact trailing_append_ans _ _
  · exact trailing_append_ans _ _

/-! ### Dependency soundness -/

theorem nodeBytes_update (rest : RIdx → OracleAnswer) (ch : Fin 2 → RIdx) (q : RIdx)
    (u : OracleAnswer) (h : ∀ j, ch j ≠ q) :
    nodeBytes (Function.update rest q u) ch = nodeBytes rest ch := by
  simp only [nodeBytes, Function.update_of_ne (h _)]

theorem gram_rest_update (pub : List UInt8) (vtag : UInt8) (lv : Fin 3 → Fib → List UInt8)
    (sec : SecP) (d : OracleAnswer) (rest : RIdx → OracleAnswer) (q : RIdx) (u : OracleAnswer)
    (c : CPos E₁ E₂) (h : ¬ depS c (.inr q)) :
    gram pub vtag lv sec d (Function.update rest q u) c = gram pub vtag lv sec d rest c := by
  have ne : ∀ r : RIdx, (Sum.inr q : Src) ≠ .inr r → r ≠ q := fun r hr e => hr (by rw [e])
  rcases c with T | (c | c) | (b | i | ⟨T, v⟩ | ⟨T, v⟩ | ⟨T, n⟩)
  · exact nodeBytes_update _ _ _ _ (fun j => ne _ (fun e => h ⟨j, e⟩))
  · simp only [gram, Function.update_of_ne (ne _ h)]
  · simp only [gram, Function.update_of_ne (ne _ h)]
  · by_cases hb : b.val = 0
    · simp only [gram, hb, if_true]
    · simp only [depS, hb, if_false, not_or] at h
      simp only [gram, hb, if_false, Function.update_of_ne (ne _ h.2)]
  · by_cases h2 : i.val = 2
    · simp only [depS, h2, if_true, not_or] at h
      have h0 : i.val ≠ 0 := by omega
      have h1 : i.val ≠ 1 := by omega
      simp only [gram, h0, h1, if_false, Function.update_of_ne (ne _ h.1), Function.update_of_ne (ne _ h.2)]
    · simp only [depS, h2, if_false, not_or] at h
      by_cases h0 : i.val = 0
      · simp only [gram, h0, if_true, Function.update_of_ne (ne _ h.2.2)]
      · have h1 : i.val = 1 := by omega
        simp only [gram, h0, h1, if_true, if_false, Function.update_of_ne (ne _ h.2.2)]
  · simp only [depS, not_or] at h
    simp only [gram, Function.update_of_ne (ne _ h.2.2)]
  · simp only [gram, Function.update_of_ne (ne _ h)]
  · exact nodeBytes_update _ _ _ _ (fun j => ne _ (fun e => h ⟨j, e⟩))

theorem gram_sec_update (pub : List UInt8) (vtag : UInt8) (lv : Fin 3 → Fib → List UInt8)
    (sec : SecP) (d : OracleAnswer) (rest : RIdx → OracleAnswer) (i : Fin 3) (z : NZ)
    (c : CPos E₁ E₂) (h : ¬ depS c (.inl i)) :
    gram pub vtag lv (Function.update sec i z) d rest c = gram pub vtag lv sec d rest c := by
  have ne : ∀ r : Fin 3, (Sum.inl i : Src) ≠ .inl r → r ≠ i := fun r hr e => hr (by rw [e])
  rcases c with T | (c | c) | (b | k | ⟨T, v⟩ | ⟨T, v⟩ | ⟨T, n⟩)
  · rfl
  · rfl
  · rfl
  · by_cases hb : b.val = 0
    · simp only [depS, hb, if_true] at h
      simp only [gram, hb, if_true, Function.update_of_ne (ne _ h)]
    · simp only [depS, hb, if_false, not_or] at h
      simp only [gram, hb, if_false, Function.update_of_ne (ne _ h.1)]
  · by_cases h2 : k.val = 2
    · have h0 : k.val ≠ 0 := by omega
      have h1 : k.val ≠ 1 := by omega
      simp only [gram, h0, h1, if_false]
    · simp only [depS, h2, if_false, not_or] at h
      by_cases h0 : k.val = 0
      · simp only [gram, h0, if_true, Function.update_of_ne (ne _ h.1), Function.update_of_ne (ne _ h.2.1)]
      · have h1 : k.val = 1 := by omega
        simp only [gram, h0, h1, if_true, if_false, Function.update_of_ne (ne _ h.1),
          Function.update_of_ne (ne _ h.2.1)]
  · simp only [depS, not_or] at h
    simp only [gram, Function.update_of_ne (ne _ h.1), Function.update_of_ne (ne _ h.2.1)]
  · rfl
  · rfl

end Gram

#print axioms gram
#print axioms slice_mid
#print axioms fld_gram
#print axioms gram_rest_update
#print axioms gram_sec_update
#print axioms child_bound0
#print axioms child_bound
#print axioms nodeBytes_update
end R1Z.LayoutR1PBin
