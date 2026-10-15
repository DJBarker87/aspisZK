import R1SpendExtraction
import R0C.V3.Q22Law

/-! A deterministic support consequence of the existing spend extraction
theorem, followed by the existing successful q22-containment bound. This is
not an FS soundness or source-correspondence theorem. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.SpendFailureSupport

open R0P R0P.SemSource R0P.Mask R0P.Sumcheck Polynomial
open AspisCircleGroupOrder
open AspisV8R19 AspisV8R19.DuplexFrames AspisV8R19.CausalFirstHitUnionBound
open R0C.V3.Q22

variable {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod P) E]

def drows (pub : Public E) (d : AspisR1.MatchingSupport.Data E)
    (inactive : Finset (Fin 1024)) (alpha : Fin 10 → E)
    (circle : Fin 2 → Fin 1024 → E) : AspisR1.MatchingSupport.Data E :=
  AspisR1.RawOpening.withRows (RingHom.id E)
    (AspisR1.SemanticOpening.rows inactive (SemanticTransport.points alpha)
      (SemSource.libraWeight alpha) circle) d

/-- If the checked R1 extraction premises hold but no committed candidate has
the resulting spend facts, the matching support is below its extraction
threshold. -/
theorem matchingSet_card_le
    (prime : Nat) [CharP E prime] (hprime : prime = 2^31-1)
    (S : Fin 29 → Subfield E) (F : Subfield E)
    (lanesF : ∀ l : Fin 29, l.val < 26 → S l = F)
    (B : PackBasis F) (pub : Public E) (pubTyped : PublicBase F pub)
    (d : AspisR1.MatchingSupport.Data E)
    (typed : AspisR1.CandidateDescent.WordTyped S d.W)
    (inactive : Finset (Fin 1024)) (circle : Fin 2 → Fin 1024 → E)
    (pre : Fin 14 → E) (eta claim : E) (alpha : Fin 10 → E)
    (polys : Fin 10 → E[X])
    (hgood : AspisR1.MatchingSupport.Good (drows pub d inactive alpha circle))
    (haccepted : AspisR1.MatchingSupport.AcceptedPairing
      (drows pub d inactive alpha circle))
    (checks : sumcheckChecksZ (maskClaimsR0 B) pub B pre eta claim alpha polys
      (fun j l => d.Y ⟨j.val, by omega⟩ l) (d.Y 3))
    (outside : ∀ m ∈ AspisR1.ConcreteBinding.candidates d.W,
      MaskedSemantic.OutsideBad pub B (rowsOf rowEquiv m) pre eta claim alpha polys)
    (hnot : ¬ ∃ m ∈ AspisR1.ConcreteBinding.candidates d.W,
      (ProductionHolds pub (pre 0) (pre 1) (rowsOf rowEquiv m) ∧
        CopyLinkBalance pub (rowsOf rowEquiv m)) ∧
      SpendSemantics.NoteFacts pub (rowsOf rowEquiv m)) :
    (AspisR1.MatchingSupport.matchingSet (drows pub d inactive alpha circle)).card ≤ 9557 := by
  by_contra hlarge
  have hcard : 9558 ≤
      (AspisR1.MatchingSupport.matchingSet (drows pub d inactive alpha circle)).card := by
    omega
  exact hnot (AspisR1.SpendExtraction.large_matching_extracts prime hprime S F lanesF B
    pub pubTyped d typed inactive circle pre eta claim alpha polys hgood haccepted hcard
    checks outside)

/-- The matching-support conclusion gives the old q22 theorem's successful
22-element containment bound, uniformly in its initial state. -/
set_option maxRecDepth 4096 in
theorem matchingSet_q22_successful_containment_bound
    (prime : Nat) [CharP E prime] (hprime : prime = 2^31-1)
    (S : Fin 29 → Subfield E) (F : Subfield E)
    (lanesF : ∀ l : Fin 29, l.val < 26 → S l = F)
    (B : PackBasis F) (pub : Public E) (pubTyped : PublicBase F pub)
    (d : AspisR1.MatchingSupport.Data E)
    (typed : AspisR1.CandidateDescent.WordTyped S d.W)
    (inactive : Finset (Fin 1024)) (circle : Fin 2 → Fin 1024 → E)
    (pre : Fin 14 → E) (eta claim : E) (alpha : Fin 10 → E)
    (polys : Fin 10 → E[X])
    (hgood : AspisR1.MatchingSupport.Good (drows pub d inactive alpha circle))
    (haccepted : AspisR1.MatchingSupport.AcceptedPairing
      (drows pub d inactive alpha circle))
    (checks : sumcheckChecksZ (maskClaimsR0 B) pub B pre eta claim alpha polys
      (fun j l => d.Y ⟨j.val, by omega⟩ l) (d.Y 3))
    (outside : ∀ m ∈ AspisR1.ConcreteBinding.candidates d.W,
      MaskedSemantic.OutsideBad pub B (rowsOf rowEquiv m) pre eta claim alpha polys)
    (hnot : ¬ ∃ m ∈ AspisR1.ConcreteBinding.candidates d.W,
      (ProductionHolds pub (pre 0) (pre 1) (rowsOf rowEquiv m) ∧
        CopyLinkBalance pub (rowsOf rowEquiv m)) ∧
      SpendSemantics.NoteFacts pub (rowsOf rowEquiv m)) :
    ∀ s,
      chainE
          (fun bs xs => indicator
            ((chalSet (scanOut 8 q0 bs xs s).1).card = 22 ∧
              chalSet (scanOut 8 q0 bs xs s).1 ⊆
                  AspisR1.MatchingSupport.matchingSet
                    (drows pub d inactive alpha circle))) 8 ≤
        (Nat.choose 9557 22 : ℚ) / (Nat.choose 262144 22 : ℚ) := by
  intro s
  exact q22_bound s
    (AspisR1.MatchingSupport.matchingSet (drows pub d inactive alpha circle))
    (matchingSet_card_le prime hprime S F lanesF B pub pubTyped d typed inactive circle
      pre eta claim alpha polys hgood haccepted checks outside hnot)

#print axioms matchingSet_card_le
#print axioms matchingSet_q22_successful_containment_bound

end AspisR1.SpendFailureSupport
end
