import BinMerkleTable

/-! Extensionality for finite recorded-node lookups and their deterministic
path walks. The list membership and per-digest uniqueness assumptions are
explicit; this module derives neither. -/
set_option autoImplicit false
namespace AspisR1.RWireMerkleNodeLookupExt

open BinMerkle32Path BinMerkleTable

theorem lookup_some_iff (nodes : Nodes) (d : Digest) (cs : Children)
    (huniq : ∀ cs1 cs2 digest, (cs1, digest) ∈ nodes →
      (cs2, digest) ∈ nodes → cs1 = cs2) :
    lookup nodes d = some cs ↔ (cs, d) ∈ nodes := by
  constructor
  · exact lookup_mem
  · intro hmem
    obtain ⟨cs', hlookup⟩ := lookup_exists hmem
    have hmem' := lookup_mem hlookup
    have heq := huniq cs' cs d hmem' hmem
    simpa [heq] using hlookup

theorem lookup_eq (nodes1 nodes2 : Nodes)
    (hmem : ∀ cs digest, (cs, digest) ∈ nodes1 ↔ (cs, digest) ∈ nodes2)
    (huniq : ∀ cs1 cs2 digest, (cs1, digest) ∈ nodes1 →
      (cs2, digest) ∈ nodes1 → cs1 = cs2) :
    ∀ digest, lookup nodes1 digest = lookup nodes2 digest := by
  have huniq2 : ∀ cs1 cs2 digest, (cs1, digest) ∈ nodes2 →
      (cs2, digest) ∈ nodes2 → cs1 = cs2 := by
    intro cs1 cs2 digest h1 h2
    exact huniq cs1 cs2 digest ((hmem cs1 digest).mpr h1)
      ((hmem cs2 digest).mpr h2)
  intro digest
  cases hleft : lookup nodes1 digest with
  | none =>
      cases hright : lookup nodes2 digest with
      | none => rfl
      | some cs2 =>
          have hmem2 := (lookup_some_iff nodes2 digest cs2 huniq2).mp hright
          have hmem1 := (hmem cs2 digest).mpr hmem2
          have hsome := (lookup_some_iff nodes1 digest cs2 huniq).mpr hmem1
          rw [hleft] at hsome
          cases hsome
  | some cs1 =>
      have hmem1 := (lookup_some_iff nodes1 digest cs1 huniq).mp hleft
      have hmem2 := (hmem cs1 digest).mp hmem1
      exact ((lookup_some_iff nodes2 digest cs1 huniq2).mpr hmem2).symm

theorem walk_eq (nodes1 nodes2 : Nodes)
    (hmem : ∀ cs digest, (cs, digest) ∈ nodes1 ↔ (cs, digest) ∈ nodes2)
    (huniq : ∀ cs1 cs2 digest, (cs1, digest) ∈ nodes1 →
      (cs2, digest) ∈ nodes1 → cs1 = cs2) :
    ∀ slots root, walk nodes1 slots root = walk nodes2 slots root := by
  have hlookup := lookup_eq nodes1 nodes2 hmem huniq
  intro slots
  induction slots with
  | nil => intro root; rfl
  | cons slot slots ih =>
      intro root
      simp only [walk, ih root]
      cases hrec : walk nodes2 slots root with
      | none => rfl
      | some parent =>
          exact congrArg (fun o : Option Children => o.map (fun cs => cs slot))
            (hlookup parent)

#print axioms lookup_eq
#print axioms walk_eq

#print axioms lookup_some_iff
end AspisR1.RWireMerkleNodeLookupExt
