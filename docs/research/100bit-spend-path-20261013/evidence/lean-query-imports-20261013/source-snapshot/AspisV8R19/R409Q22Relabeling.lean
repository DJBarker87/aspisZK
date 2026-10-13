import AspisV8R19.R407Q22CandidateKernel
import Mathlib.Logic.Equiv.Basic

/-! Exact relabeling symmetry of the bounded q22 independent-answer kernel.
Stopping, error counts, and the 64-draw limit remain unchanged. This is not
yet a successful-query uniformity or shared-oracle probability bound. -/
set_option autoImplicit false
namespace AspisV8R19.R409Q22Relabeling
open Q22WordScan R407Q22CandidateKernel OracleResampling
noncomputable section

def renameState (f : Nat ≃ Nat) (q : ScanState) : ScanState :=
  ⟨q.accepted.map f,q.draws⟩

def renameResult (f : Nat ≃ Nat) : Except Nat (List Nat) → Except Nat (List Nat)
  | .error n => .error n
  | .ok xs => .ok (xs.map f)

theorem keep_rename (f : Nat ≃ Nat) (xs : List Nat) (x : Nat) :
    keep (xs.map f) (f x) = (keep xs x).map f := by
  have hm : f x ∈ xs.map f ↔ x ∈ xs := by
    constructor
    · intro h
      obtain ⟨y,hy,he⟩ := List.mem_map.mp h
      exact (f.injective he) ▸ hy
    · exact List.mem_map_of_mem
  by_cases h : x ∈ xs <;> simp [keep,hm,h]

theorem scan_rename (f : Nat ≃ Nat) (q : ScanState) (xs : List Nat) :
    scan (renameState f q) (xs.map f) =
      (renameState f (scan q xs).1,(scan q xs).2) := by
  induction xs generalizing q with
  | nil => rfl
  | cons x xs ih =>
      by_cases stop : q.accepted.length = 22 ∨ q.draws = 64
      · simp [scan,renameState,stop]
      · simp only [List.map_cons,scan,renameState,List.length_map,if_neg stop]
        rw [keep_rename]
        exact ih ⟨keep q.accepted x,q.draws+1⟩

theorem finish_rename (f : Nat ≃ Nat) (q : ScanState) :
    finish (renameState f q) = renameResult f (finish q) := by
  by_cases h : q.accepted.length = 22 <;> simp [finish,renameState,renameResult,h]

def extend (e : Equiv.Perm (Fin (2^18))) : Equiv.Perm Nat :=
  e.extendDomain Fin.equivSubtype

theorem extend_value (e : Equiv.Perm (Fin (2^18))) (x : Fin (2^18)) :
    extend e x.val = (e x).val := by
  exact e.extendDomain_apply_image (Fin.equivSubtype (n := 2^18)) x

def blockPerm (e : Equiv.Perm (Fin (2^18))) :
    Equiv.Perm (Fin 8 → Fin (2^18)) := Equiv.piCongrRight (fun _ => e)

theorem block_values (e : Equiv.Perm (Fin (2^18))) (c : Fin 8 → Fin (2^18)) :
    List.ofFn (fun j => (blockPerm e c j).val) =
      (List.ofFn (fun j => (c j).val)).map (extend e) := by
  rw [List.map_ofFn]
  congr 1
  funext j
  exact (extend_value e (c j)).symm

theorem candidate_kernel_rename (e : Equiv.Perm (Fin (2^18))) (n : Nat)
    (q : ScanState) (test : Except Nat (List Nat) → ℚ) :
    candidateKernel n (renameState (extend e) q) test =
      candidateKernel n q (fun r => test (renameResult (extend e) r)) := by
  induction n generalizing q with
  | zero => simp only [candidateKernel,finish_rename]
  | succ n ih =>
      have hdraw : (renameState (extend e) q).draws = q.draws := rfl
      by_cases hd : q.draws < 64
      · simp only [candidateKernel,hdraw,if_pos hd]
        rw [← mean_equiv (blockPerm e) (fun c : Fin 8 → Fin (2^18) =>
          let r := scan (renameState (extend e) q) (List.ofFn (fun j => (c j).val))
          if r.2 then test (finish r.1) else candidateKernel n r.1 test)]
        apply mean_congr
        intro c
        rw [block_values,scan_rename]
        simp only [finish_rename,ih]
      · simp only [candidateKernel,hdraw,if_neg hd]
        exact congrArg test (finish_rename (extend e) q)

theorem empty_kernel_invariant (e : Equiv.Perm (Fin (2^18))) (n : Nat)
    (test : Except Nat (List Nat) → ℚ) :
    candidateKernel n ⟨[],0⟩ test =
      candidateKernel n ⟨[],0⟩ (fun r => test (renameResult (extend e) r)) :=
  candidate_kernel_rename e n ⟨[],0⟩ test

#print axioms keep_rename
#print axioms scan_rename
#print axioms finish_rename
#print axioms extend_value
#print axioms block_values
#print axioms candidate_kernel_rename
#print axioms empty_kernel_invariant
end
end AspisV8R19.R409Q22Relabeling
