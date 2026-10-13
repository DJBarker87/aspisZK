import R1MaskedSemantic
import R1SpendSemantics

/-! The existing R1 candidate extraction now supplies bounded integer
conservation, the input note, and both output-note bindings. Its opening and
semantic bad-event premises are unchanged. This is not an append-transition,
shared-oracle soundness, source-refinement, or zero-knowledge theorem. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.SpendExtraction
open R0P R0P.SemSource R0P.Mask R0P.Sumcheck Polynomial
open AspisCircleGroupOrder

variable {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod P) E]

/-- Accepts the checked semantic-prefix extraction result verbatim, without
adding any premise about the spend values or output notes. -/
theorem strengthen_candidate_result (prime : Nat) [CharP E prime]
    (hprime : prime = 2^31-1) (pub : Public E)
    (W : Fin 29 → AspisR1.MatchingSupport.InitialWord E) (lam chi : E)
    (h : ∃ m ∈ AspisR1.ConcreteBinding.candidates W,
      (ProductionHolds pub lam chi (rowsOf rowEquiv m) ∧
        CopyLinkBalance pub (rowsOf rowEquiv m)) ∧
      InputNoteExtracted pub (rowsOf rowEquiv m)) :
    ∃ m ∈ AspisR1.ConcreteBinding.candidates W,
      (ProductionHolds pub lam chi (rowsOf rowEquiv m) ∧
        CopyLinkBalance pub (rowsOf rowEquiv m)) ∧
      SpendSemantics.NoteFacts pub (rowsOf rowEquiv m) := by
  obtain ⟨m, hm, hprod, _⟩ := h
  exact ⟨m, hm, hprod,
    SpendSemantics.of_production prime hprime pub (rowsOf rowEquiv m) lam chi hprod⟩

theorem large_matching_extracts (prime : Nat) [CharP E prime]
    (hprime : prime = 2^31-1) (S : Fin 29 → Subfield E)
    (F : Subfield E) (lanesF : ∀ l : Fin 29, l.val < 26 → S l = F)
    (B : PackBasis F) (pub : Public E) (pubTyped : PublicBase F pub)
    (d : AspisR1.MatchingSupport.Data E)
    (typed : AspisR1.CandidateDescent.WordTyped S d.W)
    (inactive : Finset (Fin 1024)) (circle : Fin 2 → Fin 1024 → E)
    (pre : Fin 14 → E) (eta claim : E) (alpha : Fin 10 → E)
    (polys : Fin 10 → E[X])
    (hgood : AspisR1.MatchingSupport.Good
      (AspisR1.RawOpening.withRows (RingHom.id E)
        (AspisR1.SemanticOpening.rows inactive (SemanticTransport.points alpha)
          (SemSource.libraWeight alpha) circle) d))
    (haccepted : AspisR1.MatchingSupport.AcceptedPairing
      (AspisR1.RawOpening.withRows (RingHom.id E)
        (AspisR1.SemanticOpening.rows inactive (SemanticTransport.points alpha)
          (SemSource.libraWeight alpha) circle) d))
    (hcard : 9558 ≤ (AspisR1.MatchingSupport.matchingSet
      (AspisR1.RawOpening.withRows (RingHom.id E)
        (AspisR1.SemanticOpening.rows inactive (SemanticTransport.points alpha)
          (SemSource.libraWeight alpha) circle) d)).card)
    (checks : sumcheckChecksZ (maskClaimsR0 B) pub B pre eta claim alpha polys
      (fun j l => d.Y ⟨j.val, by omega⟩ l) (d.Y 3))
    (outside : ∀ m ∈ AspisR1.ConcreteBinding.candidates d.W,
      MaskedSemantic.OutsideBad pub B (rowsOf rowEquiv m) pre eta claim alpha polys) :
    ∃ m ∈ AspisR1.ConcreteBinding.candidates d.W,
      (ProductionHolds pub (pre 0) (pre 1) (rowsOf rowEquiv m) ∧
        CopyLinkBalance pub (rowsOf rowEquiv m)) ∧
      SpendSemantics.NoteFacts pub (rowsOf rowEquiv m) := by
  exact strengthen_candidate_result prime hprime pub d.W (pre 0) (pre 1)
    (MaskedSemantic.large_matching_extracts prime hprime S F lanesF B pub pubTyped
      d typed inactive circle pre eta claim alpha polys hgood haccepted hcard checks outside)

#print axioms strengthen_candidate_result
#print axioms large_matching_extracts
end AspisR1.SpendExtraction
end
