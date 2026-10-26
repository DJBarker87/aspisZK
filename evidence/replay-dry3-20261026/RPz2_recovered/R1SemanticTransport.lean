import R1SemanticOpening
import R0P.MaskProtocol

/-! Translate the mechanical R1 D18 opening witness into the existing R0P
row-space semantic interfaces. This file does not add semantic premises. -/

set_option autoImplicit false
noncomputable section
namespace AspisR1.SemanticTransport

open AspisCircleGroupOrder
open AspisPool.AlgorithmicCircleDecoderV7

variable {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod P) E]

/-- The semantic point triple before R0's coordinate reversal. -/
def points (alpha : Fin 10 → E) : Fin 3 → Fin 10 → E :=
  ![alpha, R0P.SemSource.successorPoint alpha, R0P.SemSource.xor12Point alpha]

theorem reversePoint_points (alpha : Fin 10 → E) (j : Fin 3) :
    AspisR1.reversePoint (points alpha j) = R0P.SemSource.openingPoints alpha j := by
  fin_cases j <;> rfl

/-- The three D18 coefficient claims are exactly the R0P honest point claims
on the trace obtained by applying the row transport to the coefficient tuple. -/
theorem witness_point_claims
    (S : Fin 29 → Subfield E) (d : AspisR1.MatchingSupport.Data E)
    (alpha : Fin 10 → E) (m : AspisR1.ConcreteBinding.Tuple E)
    (hm : AspisR1.SemanticOpening.Witness S d (points alpha)
      (R0P.SemSource.libraWeight alpha) m) :
    (fun j : Fin 3 => fun l : Fin 29 => d.Y ⟨j.val, by omega⟩ l) =
      R0P.SemSource.honestClaims (R0P.SemSource.rowsOf AspisR1.rowEquiv m) alpha := by
  funext j l
  have h := hm.2.1 j l
  rw [AspisR0.Opening.dot_coeffWeight_left] at h
  rw [reversePoint_points alpha j] at h
  change d.Y ⟨j.val, by omega⟩ l =
    AspisR0.RoundNormalization.dot
      (AspisR0.Opening.eqWeight (R0P.SemSource.openingPoints alpha j))
      (fun r => m l (AspisR1.rowEquiv r))
  exact h

/-- The D18 extra row is the existing Libra-weighted extra claim on the
transported semantic trace. -/
theorem witness_extra_claims
    (S : Fin 29 → Subfield E) (d : AspisR1.MatchingSupport.Data E)
    (alpha : Fin 10 → E) (m : AspisR1.ConcreteBinding.Tuple E)
    (hm : AspisR1.SemanticOpening.Witness S d (points alpha)
      (R0P.SemSource.libraWeight alpha) m) :
    d.Y 3 = R0P.Mask.honestExtra AspisR1.rowEquiv
      (R0P.SemSource.rowsOf AspisR1.rowEquiv m) alpha := by
  funext l
  have h := hm.2.2.1 l
  change d.Y 3 l = AspisR0.RoundNormalization.dot
    (R0P.SemSource.libraWeight alpha) (m l) at h
  change d.Y 3 l = AspisR0.RoundNormalization.dot
    (R0P.Mask.libraWeight alpha)
    (R0P.SemSource.coeffsOf AspisR1.rowEquiv
      (R0P.SemSource.rowsOf AspisR1.rowEquiv m) l)
  rw [R0P.SemSource.coeffsOf_rowsOf]
  exact h

/-- Candidate encoder descent supplies the C1 base typing of the transported
row trace. -/
theorem witness_baseTyped
    (S : Fin 29 → Subfield E) (F : Subfield E)
    (lanesF : ∀ l : Fin 29, l.val < 26 → S l = F)
    (d : AspisR1.MatchingSupport.Data E) (alpha : Fin 10 → E)
    (m : AspisR1.ConcreteBinding.Tuple E)
    (hm : AspisR1.SemanticOpening.Witness S d (points alpha)
      (R0P.SemSource.libraWeight alpha) m) :
    R0P.BaseTyped F (R0P.SemSource.rowsOf AspisR1.rowEquiv m) := by
  have htyped := AspisR1.SemanticOpening.witness_rows_typed S d (points alpha)
    (R0P.SemSource.libraWeight alpha) m hm
  intro l hl r
  change m l (AspisR1.rowEquiv r) ∈ F
  have hs : m l (AspisR1.rowEquiv r) ∈ S l := htyped l r
  rw [lanesF l hl] at hs
  exact hs

#print axioms reversePoint_points
#print axioms witness_point_claims
#print axioms witness_extra_claims
#print axioms witness_baseTyped

end AspisR1.SemanticTransport
end
