import R1IncrementalJointCandidates

/-! Completeness and bounded intermediate lists for a lane-by-lane candidate
merge. The supplied per-lane lists remain an explicit interface; this file
does not implement interpolation, factorization, or a complexity model. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.IncrementalCandidateLoop

open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.InitialEncoder
open AspisR1.PartialJointList AspisR1.IncrementalJointCandidates

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

def run (W : Fin 29 → InitialWord K)
    (decoded : Fin 29 → Finset (InitialMessage K))
    (S : Finset (Fin 29)) (family : Finset (Fin 29 → InitialMessage K)) :
    List (Fin 29) → Finset (Fin 29 → InitialMessage K)
  | [] => family
  | lane :: rest => run W decoded (insert lane S)
      (advance S lane W family (decoded lane)) rest

theorem run_supported (W : Fin 29 → InitialWord K)
    (decoded : Fin 29 → Finset (InitialMessage K)) (lanes : List (Fin 29))
    (S : Finset (Fin 29)) (family : Finset (Fin 29 → InitialMessage K))
    (hzero : ∀ t ∈ family, ∀ l, l ∉ S → t l = 0) :
    ∀ t ∈ run W decoded S family lanes, ∀ l, l ∉ S ∪ lanes.toFinset → t l = 0 := by
  induction lanes generalizing S family with
  | nil => simpa [run] using hzero
  | cons lane rest ih =>
      have h := ih (insert lane S) (advance S lane W family (decoded lane))
        (advance_supported S lane W family (decoded lane) hzero)
      simpa [run, Finset.union_insert, Finset.insert_union] using h

theorem run_card_le_100 (W : Fin 29 → InitialWord K)
    (decoded : Fin 29 → Finset (InitialMessage K)) (lanes : List (Fin 29))
    (S : Finset (Fin 29)) (family : Finset (Fin 29 → InitialMessage K))
    (hzero : ∀ t ∈ family, ∀ l, l ∉ S → t l = 0)
    (hcard : family.card ≤ 100) :
    (run W decoded S family lanes).card ≤ 100 := by
  induction lanes generalizing S family with
  | nil => exact hcard
  | cons lane rest ih =>
      exact ih (insert lane S) (advance S lane W family (decoded lane))
        (advance_supported S lane W family (decoded lane) hzero)
        (advance_card_le_100 S lane W family (decoded lane) hzero)

set_option maxRecDepth 8192 in
theorem run_preserves_projection (W : Fin 29 → InitialWord K)
    (decoded : Fin 29 → Finset (InitialMessage K)) (lanes : List (Fin 29))
    (S : Finset (Fin 29)) (family : Finset (Fin 29 → InitialMessage K))
    (t : Fin 29 → InitialMessage K) (ht : t ∈ InitialResponses.Lambda W)
    (hp : projectMessage S t ∈ family)
    (hd : ∀ lane ∈ lanes, t lane ∈ decoded lane) :
    projectMessage (S ∪ lanes.toFinset) t ∈ run W decoded S family lanes := by
  induction lanes generalizing S family with
  | nil => simpa [run] using hp
  | cons lane rest ih =>
      have hp' := advance_preserves_full_projection S lane W family (decoded lane)
        t ht hp (hd lane (List.mem_cons_self))
      have h := ih (insert lane S) (advance S lane W family (decoded lane)) hp'
        (fun l hl => hd l (List.mem_cons_of_mem lane hl))
      simpa [run, Finset.union_insert, Finset.insert_union] using h

theorem run_close (W : Fin 29 → InitialWord K)
    (decoded : Fin 29 → Finset (InitialMessage K)) (lanes : List (Fin 29))
    (S : Finset (Fin 29)) (family : Finset (Fin 29 → InitialMessage K))
    (hclose : ∀ t ∈ family, 38230 ≤ (selectedSupport S W t).card) :
    ∀ t ∈ run W decoded S family lanes,
      38230 ≤ (selectedSupport (S ∪ lanes.toFinset) W t).card := by
  induction lanes generalizing S family with
  | nil => simpa [run] using hclose
  | cons lane rest ih =>
      have h := ih (insert lane S) (advance S lane W family (decoded lane))
        (fun t ht => (Finset.mem_filter.mp ht).2)
      simpa [run, Finset.union_insert, Finset.insert_union] using h

set_option maxRecDepth 8192 in
theorem full_candidate_coordinate_close (W : Fin 29 → InitialWord K)
    (t : Fin 29 → InitialMessage K) (ht : t ∈ InitialResponses.Lambda W)
    (lane : Fin 29) : t lane ∈ InitialResponses.Close (W lane) := by
  rw [InitialResponses.mem_Close]
  have hsub : AspisV6Width29CorrelatedAgreement.width29JointAgreementSet
      exactInitialEncoder W t ⊆
      AspisV5FriCoherentCandidateExtraction.agreementSet (W lane)
        (exactInitialEncoder (t lane)) := by
    intro x hx
    simp only [AspisV6Width29CorrelatedAgreement.width29JointAgreementSet,
      Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx lane⟩
  exact (InitialResponses.mem_Lambda W t).mp ht |>.trans (Finset.card_le_card hsub)

def candidates (W : Fin 29 → InitialWord K)
    (decoded : Fin 29 → Finset (InitialMessage K)) (lanes : List (Fin 29)) :
    Finset (Fin 29 → InitialMessage K) :=
  run W decoded ∅ {0} lanes

theorem candidates_card (W : Fin 29 → InitialWord K)
    (decoded : Fin 29 → Finset (InitialMessage K)) (lanes : List (Fin 29)) :
    (candidates W decoded lanes).card ≤ 100 := by
  apply run_card_le_100
  · intro t ht l hl
    have : t = 0 := Finset.mem_singleton.mp ht
    simp [this]
  · simp

set_option maxRecDepth 8192 in
theorem candidates_eq_lambda (W : Fin 29 → InitialWord K)
    (decoded : Fin 29 → Finset (InitialMessage K)) (lanes : List (Fin 29))
    (hcover : lanes.toFinset = Finset.univ)
    (hcomplete : ∀ lane, InitialResponses.Close (W lane) ⊆ decoded lane) :
    candidates W decoded lanes = InitialResponses.Lambda W := by
  classical
  have hz : ∀ t ∈ ({0} : Finset (Fin 29 → InitialMessage K)),
      38230 ≤ (selectedSupport ∅ W t).card := by
    intro t ht
    have hempty : selectedSupport ∅ W t = Finset.univ := by
      ext x
      simp only [selectedSupport, Finset.mem_filter, Finset.mem_univ,
        Finset.notMem_empty, false_implies, implies_true, and_self]
    rw [hempty, Finset.card_univ, Fintype.card_fin]
    omega
  ext t
  constructor
  · intro ht
    have h := run_close W decoded lanes ∅ {0} hz t ht
    have hsupport : selectedSupport (Finset.univ : Finset (Fin 29)) W t =
        AspisV6Width29CorrelatedAgreement.width29JointAgreementSet
          exactInitialEncoder W t := by
      ext x
      simp only [selectedSupport,
        AspisV6Width29CorrelatedAgreement.width29JointAgreementSet,
        Finset.mem_filter, Finset.mem_univ, true_and, forall_const]
    rw [InitialResponses.mem_Lambda]
    simpa [hcover, hsupport] using h
  · intro ht
    have hp : projectMessage ∅ t ∈ ({0} : Finset (Fin 29 → InitialMessage K)) := by
      apply Finset.mem_singleton.mpr
      funext lane
      simp [projectMessage]
    have h := run_preserves_projection W decoded lanes ∅ {0} t ht hp
      (fun lane _ => hcomplete lane (full_candidate_coordinate_close W t ht lane))
    simpa [hcover, projectMessage, candidates] using h

#print axioms run_supported
#print axioms run_card_le_100
#print axioms run_preserves_projection
#print axioms run_close
#print axioms full_candidate_coordinate_close
#print axioms candidates_card
#print axioms candidates_eq_lambda

end AspisR1.IncrementalCandidateLoop
end
