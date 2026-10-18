import RRPrefixCollector
import RRPartialPrefixCollector

namespace RRPartialPrefixContracts

open Polynomial
open RRDenseCoeffVector
universe u

theorem collectTotal_eq_existing {K S : Type u} (zeroTest : S → Bool)
    (children : S → List (K × S)) :
    ∀ d s, RRPartialPrefixCollector.collectTotal zeroTest children d s =
      RRPrefixCollector.collect zeroTest children d s := by
  intro d
  induction d with
  | zero => intro s; rfl
  | succ d ih => intro s; simp [RRPartialPrefixCollector.collectTotal, RRPrefixCollector.collect, ih]

theorem partial_candidate_sound {K S : Type u} [Field K]
    (zeroTest : S → Bool) (children? : S → Option (List (K × S)))
    (children : S → List (K × S)) (model : S → (K[X])[X])
    (hchildren : ∀ s cs, children? s = some cs → cs = children s)
    (hzero : ∀ s, zeroTest s = true ↔ (model s).eval 0 = 0)
    (hstep : ∀ s a t, (a,t) ∈ children s → ∀ f,
      (model t).eval f = 0 → (model s).eval (C a + X * f) = 0)
    (d : Nat) (s : S) (out : List (List K))
    (hrun : RRPartialPrefixCollector.collectPartial zeroTest children? d s = some out)
    (candidate : List K) (hmem : candidate ∈ out) :
    (model s).eval (toPolynomial candidate) = 0 := by
  have htree := RRPartialPrefixCollector.collectPartial_success_eq_total
    zeroTest children? children hchildren d s out hrun
  have hcollect : out = RRPrefixCollector.collect zeroTest children d s :=
    htree.trans (collectTotal_eq_existing zeroTest children d s)
  have hmem' : candidate ∈ RRPrefixCollector.collect zeroTest children d s := by
    rw [← hcollect]
    exact hmem
  exact RRPrefixCollector.collect_sound zeroTest children model hzero hstep d s candidate hmem' 

theorem partial_success_complete {K S : Type u} [Field K]
    (zeroTest : S → Bool) (children? : S → Option (List (K × S)))
    (children : S → List (K × S)) (model : S → (K[X])[X])
    (hchildren : ∀ s cs, children? s = some cs → cs = children s)
    (hzero : ∀ s, zeroTest s = true ↔ (model s).eval 0 = 0)
    (hstep : ∀ s f, (model s).eval f = 0 →
      ∃ a t, (a,t) ∈ children s ∧ a = f.coeff 0 ∧ (model t).eval f.divX = 0)
    (d : Nat) (s : S) (out : List (List K))
    (hrun : RRPartialPrefixCollector.collectPartial zeroTest children? d s = some out)
    (f : K[X]) (hroot : (model s).eval f = 0)
    (hbound : f = 0 ∨ f.natDegree < d) :
    ∃ candidate ∈ out, toPolynomial candidate = f := by
  have htree := RRPartialPrefixCollector.collectPartial_success_eq_total
    zeroTest children? children hchildren d s out hrun
  obtain ⟨candidate, hmem, hpoly⟩ := RRPrefixCollector.collect_complete
    zeroTest children model hzero hstep d s f hroot hbound
  refine ⟨candidate, ?_, hpoly⟩
  have hcollect : out = RRPrefixCollector.collect zeroTest children d s :=
    htree.trans (collectTotal_eq_existing zeroTest children d s)
  rw [hcollect]
  exact hmem

#print axioms partial_candidate_sound
#print axioms partial_success_complete

end RRPartialPrefixContracts
