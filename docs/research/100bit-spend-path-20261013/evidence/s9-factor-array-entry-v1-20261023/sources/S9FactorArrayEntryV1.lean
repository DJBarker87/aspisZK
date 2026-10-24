import Aeneas.Std

set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisR1S9FactorArrayEntryV1

/-- Generalizes the existing at3/set proof in
AspisR1PoseidonPreparedChannelArraySet to the constructor's 5/4-entry arrays. -/
def atN {A : Type} {N : Usize} (a : Array A N) (i : Usize) (hi : i.val < N.val) : A :=
  a.val[i.val]'(by simpa [a.property] using hi)

theorem atN_set {A : Type} {N : Usize} (a : Array A N) (i j : Usize)
    (x : A) (hi : i.val < N.val) (hj : j.val < N.val) :
    atN (a.set i x) j hj = if j.val = i.val then x else atN a j hj := by
  unfold atN
  by_cases heq : j.val = i.val
  · simp [Array.set_val_eq,heq]
  · have hne : i.val ≠ j.val := Ne.symm heq
    simp [Array.set_val_eq,List.getElem_set_ne,heq,hne]

theorem index_atN {A : Type} {N : Usize} (a : Array A N) (i : Usize)
    (hi : i.val < N.val) : Array.index_usize a i = .ok (atN a i hi) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize atN
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

theorem accepted_index_eq_atN {A : Type} {N : Usize} (a : Array A N) (i : Usize)
    (hi : i.val < N.val) (x : A) (h : Array.index_usize a i = .ok x) :
    x = atN a i hi := Result.ok.inj (h.symm.trans (index_atN a i hi))

theorem accepted_update_eq_set {A : Type} {N : Usize} (a : Array A N) (i : Usize)
    (hi : i.val < N.val) (x : A) (out : Array A N)
    (h : Array.update a i x = .ok out) : out = a.set i x := by
  obtain ⟨actual,hr,hs⟩ := WP.spec_imp_exists
    (Array.update_spec a i x (by simpa [a.property] using hi))
  have he : actual = out := Result.ok.inj (hr.symm.trans h)
  exact he ▸ hs

#print axioms atN_set
#print axioms index_atN
#print axioms accepted_index_eq_atN
#print axioms accepted_update_eq_set
end AspisR1S9FactorArrayEntryV1
