import LoopPowersCandidateSteps
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1LoopPowers

def Prefix {N : Usize} (x : field.WideExact) (a : Array field.WideExact N) (k : Nat) : Prop :=
  ∀ j : Fin N.val, j.val < k →
    Canonical (a.val[j.val]'(by rw [a.property]; exact j.isLt)) ∧
    decode (a.val[j.val]'(by rw [a.property]; exact j.isLt)) = decode x ^ j.val

theorem prefix_set {N : Usize} (x p : field.WideExact) (a : Array field.WideExact N)
    (i : Usize) (hi : i.val < N.val) (hp : Canonical p) (he : decode p = decode x ^ i.val)
    (hprefix : Prefix x a i.val) : Prefix x (a.set i p) (i.val + 1) := by
  intro j hj
  have hjset : j.val < (a.val.set i.val p).length := by simpa [a.property] using j.isLt
  change Canonical ((a.val.set i.val p)[j.val]'hjset) ∧
    decode ((a.val.set i.val p)[j.val]'hjset) = decode x ^ j.val
  by_cases hij : i.val = j.val
  · have hs : (a.val.set i.val p)[j.val]'hjset = p := by
      have hv := List.getElem_set_self (l := a.val) (i := i.val) (a := p)
        (by simpa [a.property] using hi)
      simpa [hij] using hv
    rw [hs]
    exact ⟨hp,by simpa only [hij] using he⟩
  · have hs : (a.val.set i.val p)[j.val]'hjset =
        a.val[j.val]'(by rw [a.property]; exact j.isLt) := by
      exact List.getElem_set_ne (l := a.val) (i := i.val) (j := j.val) hij hjset
    rw [hs]
    exact hprefix j (by omega)

#print axioms prefix_set
end AspisR1LoopPowers
