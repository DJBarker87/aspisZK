import R0P.Poseidon
import R0P.PositivityChain
import R0P.Schedule
import R0P.Digest

/-! Lead: the input-note semantic model and the extraction obligation.

Sources: poseidon2.rs:511–529 (`hash_fields_with_trace`: lanes 8/9 carry
domain and length, rate-8 additive absorption, no padding, digest = lanes
0–7); poseidon2.rs:464–465 and pair_forest_trace.rs:126–195
(`merkle_node_compress_v3`: left in lanes 0–7, right in lanes 8–15 with the
tweak added to lane 15); spend.rs:14–16,146–167 (domains, note layout
owner_key ‖ value ‖ asset ‖ salt, length 18); pair_forest_hiding.rs:38–72
(24 private directions, path rows 1/5/9/13 of blocks 57–62).

The tweak is written as the registry constant: pattern 10 (C:21) offsets
lane 15 by 1051521018 = p − 0x4153_1005, so in-trace lane 15 is
`right 7 − 1051521018`. Under `CharP K (2^31−1)` this is `right 7 + 0x4153_1005`. -/
set_option autoImplicit false
namespace R0P
variable {K : Type} [Field K]

/-- poseidon2.rs:515–517. -/
def spongeInit (domain len : K) : Fin 16 → K :=
  fun l => if l = 8 then domain else if l = 9 then len else 0

/-- poseidon2.rs:522–524, one rate-8 chunk added into lanes 0–7. -/
def absorb (s : Fin 16 → K) (chunk : Fin 8 → K) : Fin 16 → K :=
  fun l => if h : l.val < 8 then s l + chunk ⟨l.val, h⟩ else s l

def spongeStep (s : Fin 16 → K) (chunk : Fin 8 → K) : Fin 16 → K :=
  poseidonPermutation (absorb s chunk)

/-- poseidon2.rs:528, lanes 0–7. -/
def digestOf (s : Fin 16 → K) : Digest K := fun i => s ⟨i.val, by omega⟩

/-- spend.rs:14, `hash_owner_key sk` for an 8-word key. -/
def ownerKey (sk : Fin 8 → K) : Digest K :=
  digestOf (spongeStep (spongeInit 0x4153_0001 8) sk)

/-- spend.rs:15, `hash_nullifier (sk ‖ salt)`, length 16. -/
def nullifierHash (sk salt : Fin 8 → K) : Digest K :=
  digestOf (spongeStep (spongeStep (spongeInit 0x4153_0002 16) sk) salt)

/-- spend.rs:150–167, `hash_fields DOMAIN_NOTE (pk ‖ value ‖ asset ‖ salt)`,
length 18: chunks pk, (value, asset, salt 0–5), (salt 6–7, 0⁶). -/
def noteCommitment (pk : Fin 8 → K) (value asset : K) (salt : Fin 8 → K) : Digest K :=
  let chunk2 : Fin 8 → K := fun i =>
    if i.val = 0 then value else if i.val = 1 then asset else salt ⟨i.val - 2, by omega⟩
  let chunk3 : Fin 8 → K := fun i => if h : i.val < 2 then salt ⟨i.val + 6, by omega⟩ else 0
  digestOf (spongeStep (spongeStep (spongeStep (spongeInit 0x4153_0003 18) pk) chunk2) chunk3)

/-- pair_forest_trace.rs:168–175 as the trace carries it (C:21 offset). -/
def nodeCompress (left right : Fin 8 → K) : Digest K :=
  digestOf (poseidonPermutation (fun l =>
    if h : l.val < 8 then left ⟨l.val, h⟩
    else if l.val = 15 then right 7 - (1051521018 : K)
    else right ⟨l.val - 8, by omega⟩))

/-- pair_forest_trace.rs:152–156 with Path's bit convention: bit = 0 puts the
current digest on the left. -/
def merkleStep (cur : Digest K) (bit : Bool) (sibling : Digest K) : Digest K :=
  if bit then nodeCompress sibling cur else nodeCompress cur sibling

def merkleRootAux (cur : Digest K) (path : Fin 24 → Bool × Digest K) : Nat → Digest K
  | 0 => cur
  | n+1 => if h : n < 24 then merkleStep (merkleRootAux cur path n) (path ⟨n, h⟩).1 (path ⟨n, h⟩).2
      else merkleRootAux cur path n

def merkleRoot (leaf : Digest K) (path : Fin 24 → Bool × Digest K) : Digest K :=
  merkleRootAux leaf path 24

/-- The extraction obligation for the input note. Witness cells: sk at block 0
row 12 lanes 0–7; salt at block 2 row 12 lanes 2–7 and block 3 row 12 lanes
0–1; value at (63,0) lane 10 (the cell `positivity_of_balance` bounds); the
path bits at column 0 of the 24 path rows and siblings at their row+1. -/
def InputNoteExtracted (pub : Public K) (A : Trace K) : Prop :=
  ∃ sk salt : Fin 8 → K, ∃ path : Fin 24 → Bool × Digest K,
    pub.nullifier = nullifierHash sk salt ∧
    pub.anchor = merkleRoot (noteCommitment (ownerKey sk) (A 10 1008) pub.assetId salt) path

/-- Trace witness for the obligation above; stated so that G8/G9 prove the
chain against these exact cells. -/
def traceSk (A : Trace K) : Fin 8 → K := fun i => A ⟨i.val, by omega⟩ 12
def traceSalt (A : Trace K) : Fin 8 → K := fun i =>
  if h : i.val < 6 then A ⟨i.val + 2, by omega⟩ 44 else A ⟨i.val - 6, by omega⟩ 60
def pathBaseRow (level : Fin 24) : Fin 1024 :=
  ⟨16 * (57 + level.val / 4) + 1 + 4 * (level.val % 4), by omega⟩
def nodeBlock (level : Fin 24) : Fin 57 :=
  if h : level.val < 21 then ⟨4 + level.val, by omega⟩ else ⟨54 + (level.val - 21), by omega⟩
open Classical in
noncomputable def tracePath (A : Trace K) : Fin 24 → Bool × Digest K := fun level =>
  let b := pathBaseRow level
  let left : Digest K := fun i => A ⟨i.val, by omega⟩ (succRow b)
  let right : Digest K := fun i => A ⟨8 + i.val, by omega⟩ (succRow b)
  if A 0 b = 0 then (false, right) else (true, left)

theorem pathBaseRow_mem (level : Fin 24) : PathRow (pathBaseRow level) := by
  simp only [PathRow, pathBaseRow]
  omega

theorem nodeBlock_node (level : Fin 24) : ScheduleNode (nodeBlock level).val := by
  unfold ScheduleNode nodeBlock
  split <;> dsimp only <;> omega

#print axioms pathBaseRow_mem
#print axioms nodeBlock_node
end R0P
