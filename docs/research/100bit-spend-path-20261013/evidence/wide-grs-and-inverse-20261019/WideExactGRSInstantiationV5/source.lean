import Wide.GRSConversion
import WideTower

set_option autoImplicit false

namespace AspisWide.WideExactGRSInstantiation

open Polynomial
open AspisWideTower
open AspisWide.GRSConversion
open AspisWide.FinalEncoder
open AspisWide.InitialEncoder
open AspisPool.AlgorithmicCircleDecoderV7

noncomputable section

abbrev finalConversion :
    ExactGRSConversion 256 255 (AspisWide.FinalEncoder.exactFinalEncoder
      (K := WideExact)) :=
  AspisWide.GRSConversion.exactFinalGRSConversion (K := WideExact)

abbrev initialConversion :
    ExactGRSConversion 1024 1024 (AspisWide.InitialEncoder.exactInitialEncoder
      (K := WideExact)) :=
  AspisWide.GRSConversion.exactInitialGRSConversion (K := WideExact)

theorem removeMultiplierMatch {K : Type*} [Field K]
    (multiplier received encoderValue polynomialValue : K)
    (hmultiplier : multiplier ≠ 0)
    (hcoordinate : encoderValue = multiplier * polynomialValue) :
    polynomialValue = multiplier⁻¹ * received ↔ encoderValue = received := by
  have hleft : multiplier⁻¹ * multiplier = 1 := by
    rw [mul_comm]
    exact DivisionRing.mul_inv_cancel multiplier hmultiplier
  constructor
  · intro h
    rw [hcoordinate, h, ← mul_assoc,
      DivisionRing.mul_inv_cancel multiplier hmultiplier, one_mul]
  · intro h
    calc
      polynomialValue = multiplier⁻¹ * (multiplier * polynomialValue) := by
        rw [← mul_assoc, hleft, one_mul]
      _ = multiplier⁻¹ * encoderValue := by rw [← hcoordinate]
      _ = multiplier⁻¹ * received := by rw [h]

def finalWideNormalizedPair (received : FinalWord WideExact) (i : Fin 262144) :
    WideExact × WideExact :=
  (finalConversion.points i, (finalConversion.multipliers i)⁻¹ * received i)

theorem finalWide_multiplier_normalization
    (received : FinalWord WideExact) (message : FinalMessage WideExact)
    (i : Fin 262144) :
    (finalConversion.messagePolynomial message).eval (finalConversion.points i) =
        (finalConversion.multipliers i)⁻¹ * received i ↔
      AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact) message i = received i := by
  apply removeMultiplierMatch
    (finalConversion.multipliers i) (received i)
    (AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact) message i)
    ((finalConversion.messagePolynomial message).eval (finalConversion.points i))
    (finalConversion.multipliers_ne_zero i)
  simpa [generalizedReedSolomonEncode] using
    finalConversion.coordinate_identity message i

def initialWideNormalizedPair (received : InitialWord WideExact) (i : Fin 1048576) :
    WideExact × WideExact :=
  (initialConversion.points i, (initialConversion.multipliers i)⁻¹ * received i)

theorem initialWide_multiplier_normalization
    (received : InitialWord WideExact) (message : InitialMessage WideExact)
    (i : Fin 1048576) :
    (initialConversion.messagePolynomial message).eval (initialConversion.points i) =
        (initialConversion.multipliers i)⁻¹ * received i ↔
      AspisWide.InitialEncoder.exactInitialEncoder (K := WideExact) message i = received i := by
  apply removeMultiplierMatch
    (initialConversion.multipliers i) (received i)
    (AspisWide.InitialEncoder.exactInitialEncoder (K := WideExact) message i)
    ((initialConversion.messagePolynomial message).eval (initialConversion.points i))
    (initialConversion.multipliers_ne_zero i)
  simpa [generalizedReedSolomonEncode] using
    initialConversion.coordinate_identity message i

theorem finalWide_points_nodup : (List.ofFn finalConversion.points).Nodup :=
  List.nodup_ofFn_ofInjective finalConversion.points_injective

theorem initialWide_points_nodup : (List.ofFn initialConversion.points).Nodup :=
  List.nodup_ofFn_ofInjective initialConversion.points_injective

theorem finalWide_threshold_transport
    (received : FinalWord WideExact) (message : FinalMessage WideExact) :
    closeAtLeast 9558 (AspisWide.FinalEncoder.exactFinalEncoder
        (K := WideExact)) received message ↔
      closeAtLeast 9558 finalConversion.grsEncoder received message := by
  exact AspisWide.GRSConversion.exactFinal9558_transport received message

theorem finalWide_message_polynomial_complete
    (polynomial : WideExact[X]) (degree : polynomial.natDegree ≤ 255) :
    ∃ message : FinalMessage WideExact,
      finalConversion.messagePolynomial message = polynomial := by
  exact AspisWide.GRSConversion.exactFinalMessagePolynomial_complete
    (K := WideExact) polynomial degree

theorem initialWide_threshold_transport
    (received : InitialWord WideExact) (message : InitialMessage WideExact) :
    closeAtLeast 38230 (AspisWide.InitialEncoder.exactInitialEncoder
        (K := WideExact)) received message ↔
      closeAtLeast 38230 initialConversion.grsEncoder received message := by
  exact AspisWide.GRSConversion.exactInitial38230_transport received message

#print axioms finalWide_multiplier_normalization
#print axioms initialWide_multiplier_normalization
#print axioms finalWide_points_nodup
#print axioms initialWide_points_nodup
#print axioms finalWide_threshold_transport
#print axioms finalWide_message_polynomial_complete
#print axioms initialWide_threshold_transport

end
end AspisWide.WideExactGRSInstantiation
