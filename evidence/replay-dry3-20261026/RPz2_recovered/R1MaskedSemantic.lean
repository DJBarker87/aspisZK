import R1SemanticTransport
import R0P.MaskSemantics
import R0P.MaskValue

/-! Candidate-level reuse of the existing masked semantic argument. All six
bad-event exclusions are explicit and quantified over the literal R1 list in
the extraction theorem. This does not assign their probability, implement a
transcript, identify Rust bytes, or prove privacy. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace AspisR1.MaskedSemantic
open R0P R0P.SemSource R0P.Mask R0P.Sumcheck Polynomial
open AspisCircleGroupOrder

variable {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod P) E]

/-- Exactly the candidate-level exclusions used by the old semantic core.
No semantic conclusion or opening claim is included in this predicate. -/
structure OutsideBad (pub : Public E) {F : Subfield E} (B : PackBasis F)
    (t : Trace E) (pre : Fin 14 → E) (eta claim : E)
    (alpha : Fin 10 → E) (polys : Fin 10 → E[X]) : Prop where
  logup : ¬ BadLogUp pub t (pre 0) (pre 1)
  theta : ¬ BadTheta (laneOf t pub (pre 0) (pre 1) B) (pre 2)
  zc : ¬ BadZc (lanesComp (pre 2) (laneOf t pub (pre 0) (pre 1) B)) (preZc pre)
  mu : ¬ BadMu
    (mle 10 (lanesComp (pre 2) (laneOf t pub (pre 0) (pre 1) B)) (preZc pre))
    (bsumB 10 (fun b => t 26 (rowOf b)))
    (bsumB 10 (fun b =>
      (1 - copyActiveLiteral (copySelectors (rowSel (rowOf b)))) * t 26 (rowOf b)))
    (pre 13)
  eta_safe : ¬ etaBad claim (maskTotal (maskClaimsR0 B) rowEquiv t)
    (originalTotal pub B t pre) eta
  alpha_safe : ¬ badAlpha 27 10
    (virtualPolyZ (maskClaimsR0 B) rowEquiv pub B t pre eta) polys alpha

/-- Instantiate the existing degree theorem with the concrete selected mask. -/
theorem concreteMaskDegree {F : Subfield E} (B : PackBasis F) :
    MaskDegree (maskClaimsR0 B) := by
  intro π t
  exact maskClaimsR0_vdeg B π t

/-- Reuse the masked sumcheck, eta, zerocheck, lane and LogUp theorems on
one typed candidate. The accepted checks still have to come from the verifier. -/
theorem candidate_semantics (prime : Nat) [CharP E prime]
    (hprime : prime = 2^31-1) (F : Subfield E) (B : PackBasis F)
    (pub : Public E) (t : Trace E) (typed : BaseTyped F t)
    (pubTyped : PublicBase F pub) (pre : Fin 14 → E) (eta claim : E)
    (alpha : Fin 10 → E) (polys : Fin 10 → E[X])
    (checks : sumcheckChecksZ (maskClaimsR0 B) pub B pre eta claim alpha polys
      (honestClaims t alpha) (honestExtra rowEquiv t alpha))
    (outside : OutsideBad pub B t pre eta claim alpha polys) :
    (ProductionHolds pub (pre 0) (pre 1) t ∧ CopyLinkBalance pub t) ∧
      InputNoteExtracted pub t := by
  have hacc := checksAcceptZ (maskClaimsR0 B) rowEquiv pub B t pre eta claim
    alpha polys checks
  have htotal := originalTotal_zero_of_masked_accept (maskClaimsR0 B)
    (concreteMaskDegree B) rowEquiv pub B t pre eta claim alpha polys hacc
    outside.alpha_safe outside.eta_safe
  have hprod := semantic_of_total_zero prime hprime F B pub t typed pubTyped
    pre htotal outside.logup outside.theta outside.zc outside.mu
  exact ⟨hprod, semantic_extraction pub t (pre 0) (pre 1) hprod
    (extraction_step pub (pre 0) (pre 1) t)⟩

/-- The R1 opening's actual candidate supplies the semantic witness. Universal
exclusions use the already bounded joint list; no unique candidate is assumed.
The conclusion is the existing input-note relation, not full spend security. -/
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
      OutsideBad pub B (rowsOf rowEquiv m) pre eta claim alpha polys) :
    ∃ m ∈ AspisR1.ConcreteBinding.candidates d.W,
      (ProductionHolds pub (pre 0) (pre 1) (rowsOf rowEquiv m) ∧
        CopyLinkBalance pub (rowsOf rowEquiv m)) ∧
      InputNoteExtracted pub (rowsOf rowEquiv m) := by
  obtain ⟨m, hm⟩ := AspisR1.SemanticOpening.large_matching_implies_witness S d typed
    inactive (SemanticTransport.points alpha) (SemSource.libraWeight alpha) circle
    hgood haccepted hcard
  have hy := SemanticTransport.witness_point_claims S d alpha m hm
  have hx := SemanticTransport.witness_extra_claims S d alpha m hm
  have ht := SemanticTransport.witness_baseTyped S F lanesF d alpha m hm
  rw [hy, hx] at checks
  exact ⟨m, hm.1, candidate_semantics prime hprime F B pub (rowsOf rowEquiv m)
    ht pubTyped pre eta claim alpha polys checks (outside m hm.1)⟩

#print axioms concreteMaskDegree
#print axioms candidate_semantics
#print axioms large_matching_extracts
end AspisR1.MaskedSemantic
end
