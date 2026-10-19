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

/-- One 32-byte coefficient cell, represented by its fixed-width LE encoder. -/
def semanticCoeffCellBytes32
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
    {Bat : Type} [BatchedLayer K Bat]
    (π : Fin 1024 ≃ Fin 1024) (pub : Public K) (B : PackBasis F)
    (t : Trace K) (r : AffTape K F) (j : Fin 10)
    (ch : Challenges K) (encode : K → Fin 32 → UInt8) (i : Fin 28) : List UInt8 :=
  List.ofFn fun b : Fin 32 => encode (run (Bat := Bat) π pub B t ch r (.semanticCoeff j i)) b

/-- The source's 28-element value array serializes as 28 ordered 32-byte cells. -/
def semanticCoeffPayloadBytes32
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
    {Bat : Type} [BatchedLayer K Bat]
    (π : Fin 1024 ≃ Fin 1024) (pub : Public K) (B : PackBasis F)
    (t : Trace K) (r : AffTape K F) (j : Fin 10)
    (ch : Challenges K) (encode : K → Fin 32 → UInt8) : List UInt8 :=
  (List.ofFn fun i : Fin 28 => semanticCoeffCellBytes32 (Bat := Bat) π pub B t r j ch encode i).flatten

def semanticSumcheckHeader : List UInt8 := [2, 128, 3, 0, 0]

def frameSemanticCoeffRow32
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
    {Bat : Type} [BatchedLayer K Bat]
    (π : Fin 1024 ≃ Fin 1024) (pub : Public K) (B : PackBasis F)
    (t : Trace K) (r : AffTape K F) (j : Fin 10)
    (ch : Challenges K) (encode : K → Fin 32 → UInt8) : List UInt8 :=
  semanticSumcheckHeader ++ semanticCoeffPayloadBytes32 (Bat := Bat) π pub B t r j ch encode

theorem semanticCoeffPayloadBytes32_prefix_stable
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
    {Bat : Type} [BatchedLayer K Bat]
    (π : Fin 1024 ≃ Fin 1024) (pub : Public K) (B : PackBasis F)
    (t : Trace K) (r : AffTape K F) (j : Fin 10)
    (ch ch' : Challenges K) (encode : K → Fin 32 → UInt8)
    (hsem : ∀ k : Fin 25, k.val < 15 + j.val → ch.sem k = ch'.sem k) :
    semanticCoeffPayloadBytes32 (Bat := Bat) π pub B t r j ch encode =
      semanticCoeffPayloadBytes32 (Bat := Bat) π pub B t r j ch' encode := by
  unfold semanticCoeffPayloadBytes32
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  unfold semanticCoeffCellBytes32
  apply congrArg List.ofFn
  funext b
  exact congrArg (fun x => encode x b)
    (run_semanticCoeff_prefix_stable (Bat := Bat) π pub B t r j i ch ch' hsem)

theorem semanticCoeffPayloadBytes32_length
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
    {Bat : Type} [BatchedLayer K Bat]
    (π : Fin 1024 ≃ Fin 1024) (pub : Public K) (B : PackBasis F)
    (t : Trace K) (r : AffTape K F) (j : Fin 10)
    (ch : Challenges K) (encode : K → Fin 32 → UInt8) :
    (semanticCoeffPayloadBytes32 (Bat := Bat) π pub B t r j ch encode).length = 896 := by
  have hsum : ∀ n : Nat, (List.ofFn (fun _ : Fin n => 32)).sum = n * 32 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.ofFn_succ]
      simp only [List.sum_cons, ih]
      omega
  unfold semanticCoeffPayloadBytes32
  rw [List.length_flatten, List.map_ofFn]
  simp only [List.length_ofFn]
  rw [hsum 28]
  norm_num

theorem frameSemanticCoeffRow32_prefix_stable
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
    {Bat : Type} [BatchedLayer K Bat]
    (π : Fin 1024 ≃ Fin 1024) (pub : Public K) (B : PackBasis F)
    (t : Trace K) (r : AffTape K F) (j : Fin 10)
    (ch ch' : Challenges K) (encode : K → Fin 32 → UInt8)
    (hsem : ∀ k : Fin 25, k.val < 15 + j.val → ch.sem k = ch'.sem k) :
    frameSemanticCoeffRow32 (Bat := Bat) π pub B t r j ch encode =
      frameSemanticCoeffRow32 (Bat := Bat) π pub B t r j ch' encode := by
  unfold frameSemanticCoeffRow32
  exact congrArg (List.append semanticSumcheckHeader)
    (semanticCoeffPayloadBytes32_prefix_stable (Bat := Bat) π pub B t r j ch ch' encode hsem)

#print axioms semanticCoeffPayloadBytes32_prefix_stable
#print axioms semanticCoeffPayloadBytes32_length
#print axioms frameSemanticCoeffRow32_prefix_stable

end R0Z.HonestView
