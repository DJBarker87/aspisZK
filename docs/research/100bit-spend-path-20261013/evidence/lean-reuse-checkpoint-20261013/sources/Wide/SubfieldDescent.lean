import Wide.SubfieldDescentCore
import WideTower

/-! Concrete WideExact specialization of the shared subfield descent theorems. -/
set_option autoImplicit false
namespace AspisWide.SubfieldDescent
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.InitialEncoder

theorem wideInitialCodeword_subfield_descent
    (S : Subfield AspisWideTower.WideExact)
    (received : InitialWord AspisWideTower.WideExact)
    (message : InitialMessage AspisWideTower.WideExact)
    (support : Finset (Fin 1048576)) (large : 1024 < support.card)
    (agrees : ∀ x ∈ support, exactInitialEncoder message x = received x)
    (subfieldValued : ∀ x, received x ∈ S) :
    ∀ x, exactInitialEncoder message x ∈ S := by
  classical
  exact initialCodeword_subfield_descent S received message support large agrees subfieldValued

#print axioms initialMessage_fixed_of_agreement
#print axioms initialCodeword_descends
#print axioms initialCodeword_subfield_descent
#print axioms wideInitialCodeword_subfield_descent
end AspisWide.SubfieldDescent
