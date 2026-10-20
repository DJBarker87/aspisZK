import CurrentClaimPowersInstance
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentPreparedClaim.ClaimPowers
open Concrete

theorem index_success_bound {A : Type} {N : Usize} (a : Array A N) (i : Usize) (x : A)
    (h : Array.index_usize a i=Result.ok x) : i.val< N.val := by
  have hlen : i.val< a.val.length := by
    by_contra hn
    have hnone : a[i]?=none := List.getElem?_eq_none (Nat.not_lt.mp hn)
    unfold Array.index_usize at h
    rw [hnone] at h
    cases h
  simpa only [a.property] using hlen

theorem powers_success_read {N : Usize} (seed : E) (out : Array E N)
    (hseed : Canonical seed) (hpowers : powers N seed=Result.ok out)
    (i : Usize) (value : E) (hread : Array.index_usize out i=Result.ok value) :
    Canonical value ∧ decode value=decode seed^i.val := by
  obtain ⟨computed,hcomputed,hcells⟩ := powers_total_exact N seed hseed
  have he : computed=out := Result.ok.inj (hcomputed.symm.trans hpowers)
  subst computed
  have hi := index_success_bound out i value hread
  obtain ⟨v,hv,hcell⟩ := WP.spec_imp_exists
    (Array.index_usize_spec out i (by simpa only [out.property] using hi))
  have hvEq : v=value := Result.ok.inj (hv.symm.trans hread)
  have hx := hcells ⟨i.val,hi⟩
  simpa only [←hvEq,hcell] using hx

#print axioms index_success_bound
#print axioms powers_success_read
end AspisR1CurrentPreparedClaim.ClaimPowers
