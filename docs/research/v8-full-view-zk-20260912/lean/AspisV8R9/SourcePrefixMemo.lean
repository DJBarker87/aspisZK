import AspisV8R9.MemoizedExpansion

/-!
# Pinned salt-prefix address shape

The pinned helper hashes a fixed domain together with the complete attempt
binding, mask nonce, derivation tag, little-endian leaf index and seed.  C1
and C2 both call it with derivation tag `0x77`; their distinct typed-leaf tags
are outside this address.  This file instantiates only that address/repetition
shape.  It is not a seed-replacement theorem or a generated-q22 source proof.
-/
set_option autoImplicit false
namespace AspisV8R9
open AspisV8PairedCommitment
noncomputable section

abbrev Bytes32 := Fin 32 → Fin 256

structure SaltDerivationAddress where
  attemptBinding : Bytes32
  maskNonce : Bytes32
  derivationTag : Fin 256
  leafIndex : Nat
  leafSaltSeed : Bytes32

noncomputable instance : DecidableEq SaltDerivationAddress := Classical.decEq _

def spendSaltAddress (attemptBinding maskNonce leafSaltSeed : Bytes32)
    (leafIndex : Nat) : SaltDerivationAddress :=
  { attemptBinding
    maskNonce
    derivationTag := 0x77
    leafIndex
    leafSaltSeed }

theorem spendSaltAddress_index_injective
    (attemptBinding maskNonce leafSaltSeed : Bytes32) :
    Function.Injective (spendSaltAddress attemptBinding maskNonce leafSaltSeed) := by
  intro left right equal
  exact congrArg SaltDerivationAddress.leafIndex equal

/-- If an adapter invokes the same derivation address again, the memoized
ideal expansion reuses its answer and preserves it across the next address. -/
theorem repeated_then_next_memoized
    {A : Type} (table : Table SaltDerivationAddress A)
    (attemptBinding maskNonce leafSaltSeed : Bytes32)
    (fresh7 ignoredRepeat fresh8 : A) :
    let address7 := spendSaltAddress attemptBinding maskNonce leafSaltSeed 7
    let address8 := spendSaltAddress attemptBinding maskNonce leafSaltSeed 8
    let first := queryStep table address7 fresh7
    let repeated := queryStep first.2 address7 ignoredRepeat
    let next := queryStep repeated.2 address8 fresh8
    repeated = first ∧ next.2 address7 = some first.1 := by
  dsimp only
  have repeated := repeated_derivation_same_answer table
    (spendSaltAddress attemptBinding maskNonce leafSaltSeed 7)
    fresh7 ignoredRepeat
  have distinct : spendSaltAddress attemptBinding maskNonce leafSaltSeed 7 ≠
      spendSaltAddress attemptBinding maskNonce leafSaltSeed 8 := by
    intro equal
    have : (7 : Nat) = 8 := congrArg SaltDerivationAddress.leafIndex equal
    omega
  constructor
  · exact repeated
  · rw [repeated]
    exact distinct_derivation_address_preserves_old
      (queryStep table (spendSaltAddress attemptBinding maskNonce leafSaltSeed 7) fresh7).2
      (spendSaltAddress attemptBinding maskNonce leafSaltSeed 7)
      (spendSaltAddress attemptBinding maskNonce leafSaltSeed 8)
      fresh8
      (queryStep table (spendSaltAddress attemptBinding maskNonce leafSaltSeed 7) fresh7).1
      distinct
      (query_result_is_cached table
        (spendSaltAddress attemptBinding maskNonce leafSaltSeed 7) fresh7)

/-- The reconstructed selected prefix derives `salts[i]` once during C1,
retains the returned value for the C2 leaf, and installs each next index at a
distinct address. -/
theorem selected_prefix_retains_c1_c2_salt
    {A : Type} (table : Table SaltDerivationAddress A)
    (attemptBinding maskNonce leafSaltSeed : Bytes32)
    (fresh7 fresh8 : A) :
    let address7 := spendSaltAddress attemptBinding maskNonce leafSaltSeed 7
    let address8 := spendSaltAddress attemptBinding maskNonce leafSaltSeed 8
    let derived7 := queryStep table address7 fresh7
    let c1Salt := derived7.1
    let c2Salt := derived7.1
    let derived8 := queryStep derived7.2 address8 fresh8
    c1Salt = c2Salt ∧ derived8.2 address7 = some derived7.1 := by
  dsimp only
  constructor
  · rfl
  · apply distinct_derivation_address_preserves_old
    · intro equal
      have : (7 : Nat) = 8 := congrArg SaltDerivationAddress.leafIndex equal
      omega
    · exact query_result_is_cached table
        (spendSaltAddress attemptBinding maskNonce leafSaltSeed 7) fresh7

#print axioms spendSaltAddress_index_injective
#print axioms repeated_then_next_memoized
#print axioms selected_prefix_retains_c1_c2_salt
end
end AspisV8R9
