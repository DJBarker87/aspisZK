import R1IncrementalCandidateLoop

/-! A bound on the number of candidate pairs visited by the explicit
lane-by-lane merge. This counts pairs only; it is not a runtime bound for the
per-lane decoding procedure. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.IncrementalCandidateCost

open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.InitialEncoder
open AspisR1.PartialJointList AspisR1.IncrementalJointCandidates
open AspisR1.IncrementalCandidateLoop

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

def pairs (W : Fin 29 → InitialWord K)
    (decoded : Fin 29 → Finset (InitialMessage K))
    (S : Finset (Fin 29)) (family : Finset (Fin 29 → InitialMessage K)) :
    List (Fin 29) → Nat
  | [] => 0
  | lane :: rest => family.card * (decoded lane).card +
      pairs W decoded (insert lane S)
        (advance S lane W family (decoded lane)) rest

theorem pairs_le (W : Fin 29 → InitialWord K)
    (decoded : Fin 29 → Finset (InitialMessage K)) (lanes : List (Fin 29))
    (S : Finset (Fin 29)) (family : Finset (Fin 29 → InitialMessage K))
    (hzero : ∀ t ∈ family, ∀ l, l ∉ S → t l = 0)
    (hfamily : family.card ≤ 100)
    (hdecoded : ∀ lane ∈ lanes, (decoded lane).card ≤ 100) :
    pairs W decoded S family lanes ≤ lanes.length * 10000 := by
  induction lanes generalizing S family with
  | nil => simp [pairs]
  | cons lane rest ih =>
      have hstep := ih (insert lane S)
        (advance S lane W family (decoded lane))
        (advance_supported S lane W family (decoded lane) hzero)
        (advance_card_le_100 S lane W family (decoded lane) hzero)
        (fun l hl => hdecoded l (List.mem_cons_of_mem lane hl))
      have hprod : family.card * (decoded lane).card ≤ 10000 := by
        calc
          family.card * (decoded lane).card ≤ 100 * 100 :=
            Nat.mul_le_mul hfamily (hdecoded lane List.mem_cons_self)
          _ = 10000 := by norm_num
      simp only [pairs, List.length_cons]
      omega

theorem initial_pairs_le (W : Fin 29 → InitialWord K)
    (decoded : Fin 29 → Finset (InitialMessage K)) (lanes : List (Fin 29))
    (hdecoded : ∀ lane ∈ lanes, (decoded lane).card ≤ 100) :
    pairs W decoded ∅ {0} lanes ≤ lanes.length * 10000 := by
  apply pairs_le W decoded lanes ∅ {0}
  · intro t ht l hl
    have hzero : t = 0 := Finset.mem_singleton.mp ht
    simp [hzero]
  · simp
  · exact hdecoded

theorem initial_pairs_le_290000 (W : Fin 29 → InitialWord K)
    (decoded : Fin 29 → Finset (InitialMessage K)) (lanes : List (Fin 29))
    (hlen : lanes.length = 29)
    (hdecoded : ∀ lane ∈ lanes, (decoded lane).card ≤ 100) :
    pairs W decoded ∅ {0} lanes ≤ 290000 := by
  simpa [hlen] using initial_pairs_le W decoded lanes hdecoded

#print axioms pairs_le
#print axioms initial_pairs_le
#print axioms initial_pairs_le_290000

end AspisR1.IncrementalCandidateCost
end
