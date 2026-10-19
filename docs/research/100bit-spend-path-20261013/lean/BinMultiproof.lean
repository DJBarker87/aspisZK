import BinMerkleProgram
import Mathlib.Data.Finset.Sort

/-! Relational specification of the prototype's level-at-a-time binary
verifier (multiproof.rs:109-191), not extraction of its mutable arrays.
Only absent children are supplied; occupied siblings share the computed
parent. The schedule depends on indices alone. Hash reads are explicit.
The path program itself is executable (`BinMerkleProgram`). -/
set_option autoImplicit false
namespace AspisR1.BinMultiproof
open BinMerkle32Path

abbrev Active := Finset Nat
abbrev Values := Nat → Digest

def slot (i : Nat) : Fin 2 := ⟨i % 2, Nat.mod_lt _ (by decide)⟩

def slots : Nat → Nat → List (Fin 2)
  | 0, _ => []
  | depth + 1, i => slot i :: slots depth (i / 2)

def parents (active : Active) : Active := active.image (fun i => i / 2)

/-- Ascending parents, then ascending missing child slots, exactly as in
`generate` and `node_count`. No digest influences this schedule. -/
def missing (active : Active) : List Nat :=
  (active.image (fun i => i / 2)).sort (· ≤ ·) |>.flatMap fun p =>
    [2 * p, 2 * p + 1].filter fun i => i ∉ active

def levelInputs (active : Active) (cs : Nat → Children) : List (List Byte) :=
  (parents active).sort (· ≤ ·) |>.map fun p => nodeInput (cs p)

def nextValues (H : List Byte → Digest) (cs : Nat → Children) : Values :=
  fun p => H (nodeInput (cs p))

/-- A transition uses the occupied value when present and a supplied node
otherwise. Equality of the exact missing-node sequence enforces both order
and consumption. Entries outside the active parents are never read. -/
def Level (active : Active) (v : Values) (cs : Nat → Children)
    (supplied : List Digest) : Prop :=
  (∀ i ∈ active, cs (i / 2) (slot i) = v i) ∧
  supplied = (missing active).map (fun i => cs (i / 2) (slot i))

/-- Small-step acceptance semantics. Final acceptance requires exactly the
single top at index zero and no unconsumed supplied nodes. -/
inductive Accept (H : List Byte → Digest) (root : Digest) :
    Nat → Active → Values → List Digest → List (List Byte) → Prop where
  | done (v : Values) (hroot : v 0 = root) : Accept H root 0 {0} v [] []
  | step {depth : Nat} {active : Active} {v : Values}
      {cs : Nat → Children} {supplied rest : List Digest} {trace : List (List Byte)}
      (level : Level active v cs supplied)
      (tail : Accept H root depth (parents active) (nextValues H cs) rest trace) :
      Accept H root (depth + 1) active v (supplied ++ rest)
        (levelInputs active cs ++ trace)

/-- Exact number of supplied digests, determined only by query indices. -/
def nodeCount : Nat → Active → Nat
  | 0, _ => 0
  | depth + 1, active => (missing active).length + nodeCount depth (parents active)

theorem exact_consumption {H : List Byte → Digest} {root : Digest}
    {depth : Nat} {active : Active} {v : Values} {nodes : List Digest}
    {trace : List (List Byte)} (h : Accept H root depth active v nodes trace) :
    nodes.length = nodeCount depth active := by
  induction h with
  | done => rfl
  | step level tail ih =>
      simp only [List.length_append, nodeCount, level.2, List.length_map, ih]

theorem slots_length (depth i : Nat) : (slots depth i).length = depth := by
  induction depth generalizing i with
  | zero => rfl
  | succ d ih => simp [slots, ih]

theorem member_parent {active : Active} {i : Nat} (hi : i ∈ active) :
    i / 2 ∈ parents active := Finset.mem_image.mpr ⟨i, hi, rfl⟩

/-- Every accepted batch member has a single accepted path; the path's reads
are a subset of the actual level hash reads, including shared parents. -/
theorem accepted_path {H : List Byte → Digest} {root : Digest}
    {depth : Nat} {active : Active} {v : Values} {nodes : List Digest}
    {trace : List (List Byte)} (h : Accept H root depth active v nodes trace) :
    ∀ i ∈ active, ∃ path : Path (slots depth i),
      foldPath H path (v i) = root ∧ inputTrace H path (v i) ⊆ trace := by
  induction h with
  | done v hroot =>
      intro i hi
      have he : i = 0 := by simpa using hi
      subst i
      exact ⟨.nil, hroot, by simp [inputTrace]⟩
  | @step depth active v cs supplied rest trace level tail ih =>
      intro i hi
      obtain ⟨path, hp, ht⟩ := ih (i / 2) (member_parent hi)
      have hc : fillChild (slot i) (cs (i / 2)) (v i) = cs (i / 2) := by
        rw [← level.1 i hi]
        exact Function.update_eq_self _ _
      refine ⟨.cons (cs (i / 2)) path, ?_, ?_⟩
      · simpa [slots, foldPath, hc, nextValues] using hp
      · intro input hin
        simp only [inputTrace, hc, List.mem_cons] at hin
        rcases hin with he | hm
        · subst input
          apply List.mem_append_left
          apply List.mem_map.mpr
          refine ⟨i / 2, ?_, rfl⟩
          simpa using member_parent hi
        · exact List.mem_append_right _ (ht hm)

/-- Sorting/deduplication may change representation but must preserve every
original index/digest pair. Conflicting duplicates cannot satisfy this
condition. This is the postcondition of candidate.rs:104-132. -/
def Dedup (batch : List (Nat × Digest)) (active : Active) (v : Values) : Prop :=
  ∀ q ∈ batch, q.1 ∈ active ∧ v q.1 = q.2

theorem dedup_conflict {batch : List (Nat × Digest)} {active : Active} {v : Values}
    (hd : Dedup batch active v) (i : Nat) (a b : Digest)
    (ha : (i, a) ∈ batch) (hb : (i, b) ∈ batch) : a = b :=
  (hd (i, a) ha).2.symm.trans (hd (i, b) hb).2

theorem batch_accepted_paths {H : List Byte → Digest} {root : Digest}
    {depth : Nat} {active : Active} {v : Values} {nodes : List Digest}
    {trace : List (List Byte)} {batch : List (Nat × Digest)}
    (h : Accept H root depth active v nodes trace) (hd : Dedup batch active v) :
    ∀ q ∈ batch, ∃ path : Path (slots depth q.1),
      foldPath H path q.2 = root ∧ inputTrace H path q.2 ⊆ trace := by
  intro q hq
  obtain ⟨hi, hv⟩ := hd q hq
  simpa only [hv] using accepted_path h q.1 hi

/-- Candidate wrapper passes only the used prefix to the Merkle verifier.
The remainder is separately checked as zero and never supplies a sibling. -/
def PaddedAccept (H : List Byte → Digest) (root : Digest) (depth : Nat)
    (active : Active) (v : Values) (count capacity : Nat)
    (stored : List Digest) (trace : List (List Byte)) : Prop :=
  count ≤ capacity ∧ stored.length = capacity ∧
  (∀ d ∈ stored.drop count, d = fun _ => 0) ∧
  Accept H root depth active v (stored.take count) trace

theorem padding_cannot_contribute {H : List Byte → Digest} {root : Digest}
    {depth : Nat} {active : Active} {v : Values} {count capacity : Nat}
    {stored : List Digest} {trace : List (List Byte)}
    (h : PaddedAccept H root depth active v count capacity stored trace) :
    ∀ i ∈ active, ∃ path : Path (slots depth i),
      foldPath H path (v i) = root ∧ inputTrace H path (v i) ⊆ trace :=
  accepted_path h.2.2.2

theorem padded_exact_count {H : List Byte → Digest} {root : Digest}
    {depth : Nat} {active : Active} {v : Values} {count capacity : Nat}
    {stored : List Digest} {trace : List (List Byte)}
    (h : PaddedAccept H root depth active v count capacity stored trace) :
    count = nodeCount depth active := by
  have hc : count ≤ stored.length := by rw [h.2.1]; exact h.1
  have he := exact_consumption h.2.2.2
  simpa only [List.length_take, Nat.min_eq_left hc] using he

#print axioms exact_consumption
#print axioms slots_length
#print axioms member_parent
#print axioms accepted_path
#print axioms dedup_conflict
#print axioms batch_accepted_paths
#print axioms padding_cannot_contribute
#print axioms padded_exact_count
end AspisR1.BinMultiproof
