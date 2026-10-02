import AspisV8R19.R409Q22Relabeling
import Mathlib.Logic.Equiv.Fintype

/-! Equal unconditional atom masses for all legal ordered q22 lists in the
bounded independent-answer kernel. Failure mass is retained; no conditioning
on publication, source oracle freshness, or numerical loss is claimed. -/
set_option autoImplicit false
namespace AspisV8R19.R411EqualLegalQueryMass
open R409Q22Relabeling R407Q22CandidateKernel
noncomputable section

def atomMass (n : Nat) (xs : List Nat) : ℚ :=
  candidateKernel n ⟨[],0⟩ (fun r => if r = .ok xs then 1 else 0)

theorem rename_preimage (f : Nat ≃ Nat) (xs : List Nat)
    (r : Except Nat (List Nat)) :
    renameResult f r = .ok (xs.map f) ↔ r = .ok xs := by
  cases r with
  | error n => simp [renameResult]
  | ok ys =>
      simp only [renameResult,Except.ok.injEq]
      exact ⟨fun h => (List.map_injective_iff.mpr f.injective) h,
        fun h => congrArg (List.map f) h⟩

theorem atom_mass_permutation (e : Equiv.Perm (Fin (2^18))) (n : Nat)
    (xs : List Nat) : atomMass n (xs.map (extend e)) = atomMass n xs := by
  unfold atomMass
  rw [empty_kernel_invariant e n]
  simp_rw [rename_preimage]

theorem equal_legal_atom_mass (n : Nat) (xs ys : Fin 22 → Fin (2^18))
    (hx : Function.Injective xs) (hy : Function.Injective ys) :
    atomMass n (List.ofFn (fun i => (xs i).val)) =
      atomMass n (List.ofFn (fun i => (ys i).val)) := by
  obtain ⟨e,he⟩ := Equiv.Perm.exists_extending_pair xs ys hx hy
  have hm : (List.ofFn (fun i => (xs i).val)).map (extend e) =
      List.ofFn (fun i => (ys i).val) := by
    rw [List.map_ofFn]
    congr 1
    funext i
    rw [extend_value,he]
  exact ((atom_mass_permutation e n _).symm).trans (congrArg (atomMass n) hm)

#print axioms rename_preimage
#print axioms atom_mass_permutation
#print axioms equal_legal_atom_mass
end
end AspisV8R19.R411EqualLegalQueryMass
