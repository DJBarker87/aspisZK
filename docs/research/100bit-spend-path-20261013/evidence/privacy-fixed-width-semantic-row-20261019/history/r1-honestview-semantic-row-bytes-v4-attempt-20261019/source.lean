import R0Z.HonestView
import R1HonestViewSemanticCoeffPrefix

set_option autoImplicit false
noncomputable section
namespace R0Z.HonestView
open R0P R0P.SemSource R0Z.MaskLayout R0Z.ViewAffine Polynomial
open AspisPool.AlgorithmicCircleDecoderV7 AspisWide.InitialEncoder
open AspisWide.Agreement AspisR0.Opening AspisR0.Chord AspisR0.ChordGeometry
open AspisV5ComponentCConcreteFoldLinearity
open AspisR0.PolynomialPair AspisR0.RoundNormalization AspisR0.Fold

/-- The per-coefficient output of the actual typed builder, kept indexed so
its equality follows directly from the checked semanticCoeff prefix theorem. -/
def semanticCoeffCellBytes
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
    {Bat : Type} [BatchedLayer K Bat]
    (π : Fin 1024 ≃ Fin 1024) (pub : Public K) (B : PackBasis F)
    (t : Trace K) (r : AffTape K F) (j : Fin 10)
    (ch : Challenges K) (encode : K → List UInt8) (i : Fin 28) : List UInt8 :=
  encode (run (Bat := Bat) π pub B t ch r (.semanticCoeff j i))

/-- The payload byte string is the ordered concatenation of the 28 encoded
coefficients, matching `encode_values`'s source loop shape. -/
def semanticCoeffPayloadBytes
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
    {Bat : Type} [BatchedLayer K Bat]
    (π : Fin 1024 ≃ Fin 1024) (pub : Public K) (B : PackBasis F)
    (t : Trace K) (r : AffTape K F) (j : Fin 10)
    (ch : Challenges K) (encode : K → List UInt8) : List UInt8 :=
  (List.ofFn fun i : Fin 28 => semanticCoeffCellBytes (Bat := Bat) π pub B t r j ch encode i).flatten

/-- Fixed row framing appends the payload after a deterministic tag/length
header, as `wire::record` does after its row-shape checks. -/
def frameSemanticCoeffRow
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
    {Bat : Type} [BatchedLayer K Bat]
    (π : Fin 1024 ≃ Fin 1024) (pub : Public K) (B : PackBasis F)
    (t : Trace K) (r : AffTape K F) (j : Fin 10)
    (ch : Challenges K) (encode : K → List UInt8) (header : List UInt8) : List UInt8 :=
  header ++ semanticCoeffPayloadBytes (Bat := Bat) π pub B t r j ch encode

theorem semanticCoeffPayloadBytes_prefix_stable
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
    {Bat : Type} [BatchedLayer K Bat]
    (π : Fin 1024 ≃ Fin 1024) (pub : Public K) (B : PackBasis F)
    (t : Trace K) (r : AffTape K F) (j : Fin 10)
    (ch ch' : Challenges K) (encode : K → List UInt8)
    (hsem : ∀ k : Fin 25, k.val < 15 + j.val → ch.sem k = ch'.sem k) :
    semanticCoeffPayloadBytes (Bat := Bat) π pub B t r j ch encode =
      semanticCoeffPayloadBytes (Bat := Bat) π pub B t r j ch' encode := by
  unfold semanticCoeffPayloadBytes
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  unfold semanticCoeffCellBytes
  exact congrArg encode (run_semanticCoeff_prefix_stable (Bat := Bat) π pub B t r j i ch ch' hsem)

theorem frameSemanticCoeffRow_prefix_stable
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
    {Bat : Type} [BatchedLayer K Bat]
    (π : Fin 1024 ≃ Fin 1024) (pub : Public K) (B : PackBasis F)
    (t : Trace K) (r : AffTape K F) (j : Fin 10)
    (ch ch' : Challenges K) (encode : K → List UInt8) (header : List UInt8)
    (hsem : ∀ k : Fin 25, k.val < 15 + j.val → ch.sem k = ch'.sem k) :
    frameSemanticCoeffRow (Bat := Bat) π pub B t r j ch encode header =
      frameSemanticCoeffRow (Bat := Bat) π pub B t r j ch' encode header := by
  unfold frameSemanticCoeffRow
  exact congrArg (List.append header)
    (semanticCoeffPayloadBytes_prefix_stable (Bat := Bat) π pub B t r j ch ch' encode hsem)

#print axioms semanticCoeffPayloadBytes_prefix_stable
#print axioms frameSemanticCoeffRow_prefix_stable

end R0Z.HonestView
