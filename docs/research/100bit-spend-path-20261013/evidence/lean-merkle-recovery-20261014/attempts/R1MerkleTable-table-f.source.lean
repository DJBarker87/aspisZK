import R1Merkle32Path
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Basic

/-! Finite recorded eight-child tables and a purely structural path walk.
This module does not hash, parse, or assert collision freedom. -/
set_option autoImplicit false
namespace AspisR1.MerkleTable

open Merkle32Path

@[reducible] def Nodes := List (Children × Digest)

def nodeMem (nodes : Nodes) (entry : Children × Digest) : Prop :=
  List.Mem entry (nodes : List (Children × Digest))

instance : Membership (Children × Digest) Nodes where
  mem := nodeMem

def lookup : Nodes → Digest → Option Children
  | [], _ => none
  | (cs, h) :: rest, d => if h = d then some cs else lookup rest d

theorem lookup_mem {nodes : Nodes} {d : Digest} {cs : Children}
    (h : lookup nodes d = some cs) : (cs, d) ∈ nodes := by
  simp only [Membership.mem, nodeMem]
  induction nodes with
  | nil => simp [lookup] at h
  | cons entry rest ih =>
      rcases entry with ⟨recorded, root⟩
      simp only [lookup] at h
      by_cases heq : root = d
      · simp [heq] at h
        subst cs
        subst d
        simp
      · simp [heq] at h
        have hmem := ih h
        exact List.mem_cons_of_mem _ hmem

theorem lookup_exists {nodes : Nodes} {cs : Children} {d : Digest}
    (h : (cs, d) ∈ nodes) : ∃ cs', lookup nodes d = some cs' := by
  simp only [Membership.mem, nodeMem] at h
  induction nodes with
  | nil => simp at h
  | cons entry rest ih =>
      rcases entry with ⟨recorded, root⟩
      simp only [List.mem_cons] at h
      rcases h with hhead | htail
      · simp only [Prod.mk.injEq] at hhead
        rcases hhead with ⟨rfl, rfl⟩
        exact ⟨recorded, by simp [lookup]⟩
      · obtain ⟨cs', hc⟩ := ih htail
        by_cases heq : root = d
        · exact ⟨recorded, by simp [lookup, heq]⟩
        · exact ⟨cs', by simpa [lookup, heq] using hc⟩

def targets (nodes : Nodes) (root : Digest) : List Digest :=
  root :: nodes.flatMap (fun q => List.ofFn q.1)

theorem targets_length (nodes : Nodes) (root : Digest) :
    (targets nodes root).length = 1 + 8 * nodes.length := by
  simp [targets, List.length_flatMap, List.length_ofFn]
  omega

theorem root_mem_targets (nodes : Nodes) (root : Digest) :
    root ∈ targets nodes root := by
  simp [targets]

theorem child_mem_targets {nodes : Nodes} {cs : Children} {d root : Digest}
    (h : (cs, d) ∈ nodes) (slot : Fin 8) : cs slot ∈ targets nodes root := by
  simp only [Membership.mem, nodeMem] at h
  apply List.mem_cons_of_mem
  rw [List.mem_flatMap]
  refine ⟨(cs, d), h, ?_⟩
  rw [List.mem_ofFn]
  exact ⟨slot, rfl⟩

def walk (nodes : Nodes) : List (Fin 8) → Digest → Option Digest
  | [], root => some root
  | slot :: slots, root =>
      (walk nodes slots root).bind fun parent =>
        (lookup nodes parent).map fun cs => cs slot

theorem walk_mem_targets (nodes : Nodes) :
    ∀ (slots : List (Fin 8)) (root d : Digest),
      walk nodes slots root = some d → d ∈ targets nodes root := by
  intro slots
  induction slots with
  | nil =>
      intro root d h
      simp [walk] at h
      subst d
      exact root_mem_targets nodes root
  | cons slot slots ih =>
      intro root d h
      cases hrec : walk nodes slots root with
      | none => simp [walk, hrec] at h
      | some parent =>
          have hmap : (lookup nodes parent).map (fun cs => cs slot) = some d := by
            simpa [walk, hrec] using h
          cases hlookup : lookup nodes parent with
          | none => simp [hlookup] at hmap
          | some cs =>
              have hvalue : cs slot = d := by simpa [hlookup] using hmap
              have hentry := lookup_mem hlookup
              rw [← hvalue]
              exact child_mem_targets hentry slot

#print axioms lookup_mem
#print axioms lookup_exists
#print axioms targets_length
#print axioms root_mem_targets
#print axioms child_mem_targets
#print axioms walk_mem_targets

end AspisR1.MerkleTable
