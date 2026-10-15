import R1SelectedOpeningClaims
import R1OpeningPolynomialView
import R1MatchingSupport

/-! Package the selected typed payloads as the existing MatchingSupport.Data.
This is an explicit model construction from supplied payloads and words; it
does not claim source recovery, commitment correspondence, or acceptance. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.SelectedOpeningData

open AspisR1.CircleRecordCodec
open AspisR1.OpeningRecordCodec
open AspisR1.MatchingSupport

abbrev E := AspisWideTower.WideExact

structure Payloads where
  row25 : CircleRecordCodec.Payload 0
  row26 : CircleRecordCodec.Payload 1
  row27 : OpeningRecordCodec.Payload .gamma
  row28 : OpeningRecordCodec.Payload .kappa
  row29 : OpeningRecordCodec.Payload .first
  row30 : OpeningRecordCodec.Payload .second
  row31 : OpeningRecordCodec.Payload .final

/-- Construct the matching-support data using explicit external words,
functionals, and challenges together with the supplied selected payloads. -/
def data (payloads : Payloads)
    (W : Fin 29 → InitialWord E) (V : FinalWord E)
    (F : Fin 6 → Functional E) (F0 : Functional E)
    (gamma kappa alpha0 alpha1 : E) : MatchingSupport.Data E where
  W := W
  V := V
  F := F
  F0 := F0
  Y := SelectedOpeningClaims.Y payloads.row25 payloads.row26 payloads.row27
  c0 := payloads.row28
  gamma := gamma
  kappa := kappa
  alpha0 := alpha0
  alpha1 := alpha1
  p0 := OpeningPolynomialView.firstPolynomial payloads.row29
  p1 := OpeningPolynomialView.secondPolynomial payloads.row30
  f := payloads.row31

theorem data_Y (payloads : Payloads)
    (W : Fin 29 → InitialWord E) (V : FinalWord E)
    (F : Fin 6 → Functional E) (F0 : Functional E)
    (gamma kappa alpha0 alpha1 : E) :
    (data payloads W V F F0 gamma kappa alpha0 alpha1).Y =
      SelectedOpeningClaims.Y payloads.row25 payloads.row26 payloads.row27 := rfl

theorem data_c0 (payloads : Payloads)
    (W : Fin 29 → InitialWord E) (V : FinalWord E)
    (F : Fin 6 → Functional E) (F0 : Functional E)
    (gamma kappa alpha0 alpha1 : E) :
    (data payloads W V F F0 gamma kappa alpha0 alpha1).c0 = payloads.row28 := rfl

theorem data_f (payloads : Payloads)
    (W : Fin 29 → InitialWord E) (V : FinalWord E)
    (F : Fin 6 → Functional E) (F0 : Functional E)
    (gamma kappa alpha0 alpha1 : E) :
    (data payloads W V F F0 gamma kappa alpha0 alpha1).f = payloads.row31 := rfl

theorem data_p0_degree_le (payloads : Payloads)
    (W : Fin 29 → InitialWord E) (V : FinalWord E)
    (F : Fin 6 → Functional E) (F0 : Functional E)
    (gamma kappa alpha0 alpha1 : E) :
    ((data payloads W V F F0 gamma kappa alpha0 alpha1).p0).natDegree ≤ 6 :=
  OpeningPolynomialView.firstPolynomial_natDegree_le payloads.row29

theorem data_p1_degree_le (payloads : Payloads)
    (W : Fin 29 → InitialWord E) (V : FinalWord E)
    (F : Fin 6 → Functional E) (F0 : Functional E)
    (gamma kappa alpha0 alpha1 : E) :
    ((data payloads W V F F0 gamma kappa alpha0 alpha1).p1).natDegree ≤ 6 :=
  OpeningPolynomialView.secondPolynomial_natDegree_le payloads.row30

#print axioms data_Y
#print axioms data_c0
#print axioms data_f
#print axioms data_p0_degree_le
#print axioms data_p1_degree_le

end AspisR1.SelectedOpeningData
end
