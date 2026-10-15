import R1TypedRecoveryContext
import R1TypedRecoveryStability
import R1MixedLeafDecoder
import R1MerkleIndexGeometry

/-! Repackage the two C2 coordinates as their corresponding semantic words.
This is representation plumbing: paths and packed C2 leaves remain inputs. -/
set_option autoImplicit false

namespace AspisR1.RecoveredC2Semantic

open AspisR1.ExactLeafFieldCodec
open AspisR1.MixedLeafDecoder
open AspisR1.TypedRecoveredWords
open AspisR1.TypedRecoveryContext
open AspisR1.TypedRecoveryStability
open AspisR1.MerkleIndexGeometry
open AspisPool.AlgorithmicCircleDecoderV7
open R0P.SemSource

variable {E : Type} [Field E]
variable {L : Nat}

/-- The two C2 lanes, interpreted coordinatewise in the semantic field. -/
def pair (eK : QM31Exact →+* E)
    (c2Packed : Fin 262144 → Option (List Byte)) : InitialWord E × InitialWord E :=
  (fun i => eK (c2Value c2Packed i ⟨0, by decide⟩),
   fun i => eK (c2Value c2Packed i ⟨1, by decide⟩))

theorem pair_fst_fullWords (eM : M31Exact →+* E) (eK : QM31Exact →+* E)
    (c1Packed c2Packed : Fin 262144 → Option (List Byte)) :
    (pair eK c2Packed).1 = fullWords eM eK c1Packed c2Packed 26 := by
  funext i
  simp [pair, fullWords, TypedRecoveredWords.word, TypedRecoveredWords.c2Value]

theorem pair_snd_fullWords (eM : M31Exact →+* E) (eK : QM31Exact →+* E)
    (c1Packed c2Packed : Fin 262144 → Option (List Byte)) :
    (pair eK c2Packed).2 = fullWords eM eK c1Packed c2Packed 27 := by
  funext i
  simp [pair, fullWords, TypedRecoveredWords.word, TypedRecoveredWords.c2Value]

theorem pair_c2Words [Fintype E] [DecidableEq E]
    [Algebra (ZMod AspisCircleGroupOrder.P) E]
    (eM : M31Exact →+* E) (eK : QM31Exact →+* E)
    (pub : R0P.Public E) (hpub : R0P.PublicBase eM.fieldRange pub)
    (c1Packed c2Packed : Fin 262144 → Option (List Byte))
    (extraClaims : Fin 29 → E) :
    c2Words (context eM eK pub hpub c1Packed extraClaims)
      (pair eK c2Packed).1 (pair eK c2Packed).2 =
      fullWords eM eK c1Packed c2Packed := by
  rw [pair_fst_fullWords, pair_snd_fullWords]
  exact c2Words_full eM eK pub hpub c1Packed c2Packed extraClaims

theorem pair_c2Base (eM : M31Exact →+* E) (eK : QM31Exact →+* E)
    (c1Packed c2Packed : Fin 262144 → Option (List Byte)) :
    c2Base (laneSubfield eM eK) (pair eK c2Packed).1 (pair eK c2Packed).2 := by
  rw [pair_fst_fullWords, pair_snd_fullWords]
  exact c2Base_full eM eK c1Packed c2Packed

/-- Six-level paths are supplied by the existing Merkle index model. -/
def paths6C2 : Fin 262144 → List (Fin 8) :=
  fun leaf => MerkleIndexGeometry.slots 6 leaf.val

/-- The semantic pair obtained from C2 leaves recovered at the supplied trace. -/
def pairAt (eK : QM31Exact →+* E) (tr : List (Addr L × State)) (root : State) :
    InitialWord E × InitialWord E :=
  pair eK (TypedRecoveryStability.c2PackedAt tr paths6C2 root)

theorem pairAt_fst_of_decode (eK : QM31Exact →+* E)
    (tr : List (Addr L × State)) (root : State) (i : Fin 1048576) (c : C2)
    (hdecode : decodeC2At (TypedRecoveryStability.c2PackedAt tr paths6C2 root)
      (queryLeaf i) = some c) :
    (pairAt eK tr root).1 i = eK ((c (querySlot i)) ⟨0, by decide⟩) := by
  simp [pairAt, pair, c2Value, hdecode]

theorem pairAt_snd_of_decode (eK : QM31Exact →+* E)
    (tr : List (Addr L × State)) (root : State) (i : Fin 1048576) (c : C2)
    (hdecode : decodeC2At (TypedRecoveryStability.c2PackedAt tr paths6C2 root)
      (queryLeaf i) = some c) :
    (pairAt eK tr root).2 i = eK ((c (querySlot i)) ⟨1, by decide⟩) := by
  simp [pairAt, pair, c2Value, hdecode]

#print axioms pair_fst_fullWords
#print axioms pair_snd_fullWords
#print axioms pair_c2Words
#print axioms pair_c2Base
#print axioms pairAt_fst_of_decode
#print axioms pairAt_snd_of_decode

end AspisR1.RecoveredC2Semantic
