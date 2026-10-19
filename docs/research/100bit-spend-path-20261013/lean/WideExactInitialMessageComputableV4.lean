import WideExactInitialMessageComputableV1
set_option autoImplicit false
namespace AspisWide.InitialMessageComputableV4
open CompPoly
open AspisWide.InitialParityCBridgeV9
open AspisWide.InitialInverseComputable
open AspisWide.NaturalBasisTriangularV4
open AspisWide.InitialMessageComputableV1
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [NeZero (2 : K)]
def evenV (m : Fin 1024 → K) : Fin 512 → K := fun i => m ⟨2 * i.val, by omega⟩
def oddV (m : Fin 1024 → K) : Fin 512 → K := fun i => m ⟨2 * i.val + 1, by omega⟩
theorem decodeMessage_of_laneEncodings
    (nodes0 : Fin 513 → K) (nodes1 : Fin 512 → K) (q : CPolynomial K)
    (m : Fin 1024 → K)
    (h0 : decodeFractionalLiftC 512 nodes0 (evenC q) = encode 511 (evenV m))
    (h1 : decodeFractionalLiftC 511 nodes1 (oddC q) = encode 511 (oddV m)) :
    decodeMessage nodes0 nodes1 q = m := by
  funext k
  have hdiv : k.val % 2 + 2 * (k.val / 2) = k.val := Nat.mod_add_div _ _
  by_cases hk : k.val % 2 = 0
  · have hvalue : 2 * (k.val / 2) = k.val := by omega
    have hidx : (⟨2 * (k.val / 2), by omega⟩ : Fin 1024) = k := by
      apply Fin.ext
      exact hvalue
    simp [decodeMessage, hk, h0, decode_encode, evenV]
    exact congrArg m hidx
  · have hmod : k.val % 2 = 1 := by omega
    have hvalue : 2 * (k.val / 2) + 1 = k.val := by omega
    have hidx : (⟨2 * (k.val / 2) + 1, by omega⟩ : Fin 1024) = k := by
      apply Fin.ext
      exact hvalue
    simp [decodeMessage, hk, h1, decode_encode, oddV]
    exact congrArg m hidx
#print axioms decodeMessage_of_laneEncodings
end AspisWide.InitialMessageComputableV4
