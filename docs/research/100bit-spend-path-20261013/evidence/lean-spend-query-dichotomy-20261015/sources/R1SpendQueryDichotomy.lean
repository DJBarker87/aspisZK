import R1SpendFailureSupport
import R1QueryRhoAcceptance

/-! Deterministic split between the explicit rho residual exception and a
small matching support containing every accepted query. This composes existing
spend-support and rho lemmas; it is not a Fiat--Shamir acceptance theorem. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.SpendQueryDichotomy

open R0P R0P.SemSource R0P.Mask R0P.Sumcheck Polynomial
open AspisCircleGroupOrder AspisR1.MatchingSupport
open R0C.V3

variable {E K : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod P) E] [Field K] [Fintype K]
  [Algebra (ZMod P) K]

private theorem support_bound
    (prime : Nat) [CharP E prime] (hprime : prime = 2^31-1)
    (S : Fin 29 → Subfield E) (F : Subfield E)
    (lanesF : ∀ l : Fin 29, l.val < 26 → S l = F)
    (B : PackBasis F) (pub : Public E) (pubTyped : PublicBase F pub)
    (d : MatchingSupport.Data E)
    (typed : CandidateDescent.WordTyped S d.W)
    (inactive : Finset (Fin 1024)) (circle : Fin 2 → Fin 1024 → E)
    (pre : Fin 14 → E) (eta claim : E) (alpha : Fin 10 → E)
    (polys : Fin 10 → E[X])
    (hgood : Good (SpendFailureSupport.drows pub d inactive alpha circle))
    (haccepted : AcceptedPairing (SpendFailureSupport.drows pub d inactive alpha circle))
    (checks : sumcheckChecksZ (maskClaimsR0 B) pub B pre eta claim alpha polys
      (fun j l => d.Y ⟨j.val, by omega⟩ l) (d.Y 3))
    (outside : ∀ m ∈ ConcreteBinding.candidates d.W,
      MaskedSemantic.OutsideBad pub B (rowsOf rowEquiv m) pre eta claim alpha polys)
    (hnot : ¬ ∃ m ∈ ConcreteBinding.candidates d.W,
      (ProductionHolds pub (pre 0) (pre 1) (rowsOf rowEquiv m) ∧
        CopyLinkBalance pub (rowsOf rowEquiv m)) ∧
      SpendSemantics.NoteFacts pub (rowsOf rowEquiv m)) :
    (matchingSet (SpendFailureSupport.drows pub d inactive alpha circle)).card ≤ 9557 :=
  SpendFailureSupport.matchingSet_card_le prime hprime S F lanesF B pub pubTyped d
    typed inactive circle pre eta claim alpha polys hgood haccepted checks outside hnot

/-- Accepted field-level queries either hit the 21-element rho exception or
all lie in a matching support of cardinality at most 9,557. -/
theorem dichotomy
    (prime : Nat) [CharP E prime] (hprime : prime = 2^31-1)
    (S : Fin 29 → Subfield E) (F : Subfield E)
    (lanesF : ∀ l : Fin 29, l.val < 26 → S l = F)
    (B : PackBasis F) (pub : Public E) (pubTyped : PublicBase F pub)
    (d : MatchingSupport.Data E)
    (typed : CandidateDescent.WordTyped S d.W)
    (inactive : Finset (Fin 1024)) (circle : Fin 2 → Fin 1024 → E)
    (pre : Fin 14 → E) (eta claim : E) (alpha : Fin 10 → E)
    (polys : Fin 10 → E[X])
    (hgood : Good (SpendFailureSupport.drows pub d inactive alpha circle))
    (haccepted : AcceptedPairing (SpendFailureSupport.drows pub d inactive alpha circle))
    (checks : sumcheckChecksZ (maskClaimsR0 B) pub B pre eta claim alpha polys
      (fun j l => d.Y ⟨j.val, by omega⟩ l) (d.Y 3))
    (outside : ∀ m ∈ ConcreteBinding.candidates d.W,
      MaskedSemantic.OutsideBad pub B (rowsOf rowEquiv m) pre eta claim alpha polys)
    (hnot : ¬ ∃ m ∈ ConcreteBinding.candidates d.W,
      (ProductionHolds pub (pre 0) (pre 1) (rowsOf rowEquiv m) ∧
        CopyLinkBalance pub (rowsOf rowEquiv m)) ∧
      SpendSemantics.NoteFacts pub (rowsOf rowEquiv m))
    (iota : K →+* E) (q : Fin 22 → Fin 262144) (rho : K)
    (hqueries : RhoAcceptance.AcceptedQueries iota
      (SpendFailureSupport.drows pub d inactive alpha circle) q rho) :
    rho ∈ QueryResidualBridge.rhoBad iota
        (SpendFailureSupport.drows pub d inactive alpha circle) q ∨
      ((matchingSet (SpendFailureSupport.drows pub d inactive alpha circle)).card ≤ 9557 ∧
        ∀ j, q j ∈ matchingSet
          (SpendFailureSupport.drows pub d inactive alpha circle)) := by
  classical
  by_cases hmiss : ∃ j, q j ∉ matchingSet
      (SpendFailureSupport.drows pub d inactive alpha circle)
  · exact Or.inl (RhoAcceptance.accepted_mem_bad_of_query_miss iota
      (SpendFailureSupport.drows pub d inactive alpha circle) q rho hmiss hqueries)
  · right
    refine ⟨support_bound prime hprime S F lanesF B pub pubTyped d typed inactive circle
      pre eta claim alpha polys hgood haccepted checks outside hnot, ?_⟩
    intro j
    by_contra hmem
    exact hmiss ⟨j, hmem⟩

/-- With an injective query-index map, the explicit range query set has 22
members and is contained in the same small matching support in the second
branch of `dichotomy`. -/
theorem dichotomy_injective
    (prime : Nat) [CharP E prime] (hprime : prime = 2^31-1)
    (S : Fin 29 → Subfield E) (F : Subfield E)
    (lanesF : ∀ l : Fin 29, l.val < 26 → S l = F)
    (B : PackBasis F) (pub : Public E) (pubTyped : PublicBase F pub)
    (d : MatchingSupport.Data E)
    (typed : CandidateDescent.WordTyped S d.W)
    (inactive : Finset (Fin 1024)) (circle : Fin 2 → Fin 1024 → E)
    (pre : Fin 14 → E) (eta claim : E) (alpha : Fin 10 → E)
    (polys : Fin 10 → E[X])
    (hgood : Good (SpendFailureSupport.drows pub d inactive alpha circle))
    (haccepted : AcceptedPairing (SpendFailureSupport.drows pub d inactive alpha circle))
    (checks : sumcheckChecksZ (maskClaimsR0 B) pub B pre eta claim alpha polys
      (fun j l => d.Y ⟨j.val, by omega⟩ l) (d.Y 3))
    (outside : ∀ m ∈ ConcreteBinding.candidates d.W,
      MaskedSemantic.OutsideBad pub B (rowsOf rowEquiv m) pre eta claim alpha polys)
    (hnot : ¬ ∃ m ∈ ConcreteBinding.candidates d.W,
      (ProductionHolds pub (pre 0) (pre 1) (rowsOf rowEquiv m) ∧
        CopyLinkBalance pub (rowsOf rowEquiv m)) ∧
      SpendSemantics.NoteFacts pub (rowsOf rowEquiv m))
    (iota : K →+* E) (q : Fin 22 → Fin 262144) (rho : K)
    (hqueries : RhoAcceptance.AcceptedQueries iota
      (SpendFailureSupport.drows pub d inactive alpha circle) q rho)
    (hq : Function.Injective q) :
    rho ∈ QueryResidualBridge.rhoBad iota
        (SpendFailureSupport.drows pub d inactive alpha circle) q ∨
      ((matchingSet (SpendFailureSupport.drows pub d inactive alpha circle)).card ≤ 9557 ∧
        (Finset.univ.image q).card = 22 ∧
        Finset.univ.image q ⊆ matchingSet
          (SpendFailureSupport.drows pub d inactive alpha circle)) := by
  classical
  rcases dichotomy prime hprime S F lanesF B pub pubTyped d typed inactive circle
      pre eta claim alpha polys hgood haccepted checks outside hnot iota q rho hqueries with
    hbad | ⟨hcard, hall⟩
  · exact Or.inl hbad
  · right
    refine ⟨hcard, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ hq]
      simp
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨j, -, rfl⟩
      exact hall j

#print axioms dichotomy
#print axioms dichotomy_injective

end AspisR1.SpendQueryDichotomy
end
