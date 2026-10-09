import FSLiveSelectedMiddleQueryRho
import SameBodySourceRelationProducer
import SameBodyAuthenticatedIncrement

/-!
# Source-driven compact functional bytes

This leaf constructs the exact 545-byte structured-functional description and
16-byte ordinary claim from a canonical same-body word, sampled OOD data,
gamma, kappa, and the public statement point `z`.  Parsing, point decoding,
the selected inverse, and ordinary preparation are fail-closed in `fromInputs`.

The remaining literal-source boundary is the independently authenticated
producer of public `z`; it is an explicit argument, not a coherence premise.
`FSLiveSelectedMiddleQueryRho.FunctionalProducer` is total, whereas the Rust
preparation path can reject, so this leaf deliberately does not replace a
failed construction by arbitrary bytes.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000
set_option maxRecDepth 4096

namespace AspisV8Completion.SameBodyFunctionalProducerSource

open FSLiveSelectedMiddleQueryRho
open SameBodyOODData SameBodySourceRelationProducer SameBodyPublicCorrection
open SameBodyAuthenticatedIncrement SameBodyOrdinary
open AspisV8.SameBodySequentialCodec
open AspisV5ComponentCQM31Representation
open AspisPool.V7MerkleQueryGrammar

abbrev Bytes := List UInt8
abbrev K := SameBodySourceRelationProducer.K
abbrev OODResult := FSV7OODBodyScript.Result

noncomputable section

def functionalPrefix : Bytes :=
  [65,86,56,47,102,117,110,99,116,105,111,110,97,108,47,116,104,114,101,
   101,45,77,76,69,45,103,114,111,117,112,101,100,54,52,47,99,104,111,
   114,100,47,118,50]

def inactiveGroups : List Nat :=
  [0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,2,3,1,4,3,1,
   4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,2,5,5,5,5,5,5,6]

def inactiveMasks : List Nat := [59391,59390,61438,63487,63486,39321,63786]

def u16LE (value : Nat) : Bytes :=
  [UInt8.ofNat value, UInt8.ofNat (value / 256)]

def inactiveMaskBytes : Bytes :=
  inactiveGroups.flatMap fun group => u16LE (inactiveMasks.getD group 0)

def encodeList (values : List K) : Bytes :=
  values.flatMap canonicalBytes

theorem encodeList_length (values : List K) :
    (encodeList values).length = 16 * values.length := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp only [encodeList, List.flatMap_cons, List.length_append,
      canonicalBytes_length]
    change (List.flatMap canonicalBytes rest).length = 16 * rest.length at ih
    rw [ih]
    simp [Nat.mul_add, Nat.add_comm]

structure Encoded where
  description : Bytes
  claim : Bytes
  value : Corrected K
  data : AspisV8.OODInterpolant.Data (K := K)

def descriptionBytes (z : Fin 10 → K) (value : Corrected K)
    (data : AspisV8.OODInterpolant.Data (K := K)) : Bytes :=
  functionalPrefix ++
  [20,22,10,4,4,if value.prepared.useX then 1 else 0] ++
  encodeList (List.ofFn z) ++
  encodeList (List.ofFn value.prepared.scales) ++
  encodeList (List.ofFn value.prepared.abc) ++
  encodeList [value.prepared.intercept, value.prepared.slope] ++
  encodeList [data.x0, data.y0, data.x1, data.y1, data.gamma] ++
  inactiveMaskBytes

def encoded (z : Fin 10 → K) (value : Corrected K)
    (data : AspisV8.OODInterpolant.Data (K := K)) : Encoded :=
  ⟨descriptionBytes z value data, canonicalBytes value.claim, value, data⟩

def wordOfValues (values : List K) : SameBodyRelation.Word K :=
  fun i => values.getD i.val 0

/-- Total, fail-closed source constructor.  `z` is the one still-explicit
public-statement map; all private proof fields come from the canonical body. -/
def fromInputs (out : OODResult) (gamma kappa : K) (body : Bytes)
    (z : Fin 10 → K) : Option Encoded := do
  let data ← fromSampled out gamma body
  let values ← fields (body.map UInt8.toFin)
  let value ← correct ordinaryOps (wordOfValues values) gamma kappa
    (firstPoint data) (secondPoint data) z
  pure (encoded z value data)

theorem functionalPrefix_length : functionalPrefix.length = 43 := by decide
theorem inactiveGroups_length : inactiveGroups.length = 64 := by decide
theorem inactiveMaskBytes_length : inactiveMaskBytes.length = 128 := by decide

theorem descriptionBytes_length (z : Fin 10 → K) (value : Corrected K)
    (data : AspisV8.OODInterpolant.Data (K := K)) :
    (descriptionBytes z value data).length = 545 := by
  simp only [descriptionBytes, List.length_append, encodeList_length,
    List.length_ofFn, functionalPrefix_length, inactiveMaskBytes_length]
  norm_num

theorem encoded_lengths (z : Fin 10 → K) (value : Corrected K)
    (data : AspisV8.OODInterpolant.Data (K := K)) :
    (encoded z value data).description.length = 545 ∧
      (encoded z value data).claim.length = 16 := by
  exact ⟨descriptionBytes_length z value data, canonicalBytes_length value.claim⟩

theorem fromInputs_lengths (out : OODResult) (gamma kappa : K) (body : Bytes)
    (z : Fin 10 → K) (result : Encoded)
    (success : fromInputs out gamma kappa body z = some result) :
    result.description.length = 545 ∧ result.claim.length = 16 := by
  rcases dataEq : fromSampled out gamma body with _ | data
  · simp [fromInputs, dataEq] at success
  rcases valuesEq : fields (body.map UInt8.toFin) with _ | values
  · simp [fromInputs, dataEq, valuesEq] at success
  rcases valueEq : correct ordinaryOps (wordOfValues values) gamma kappa
      (firstPoint data) (secondPoint data) z with _ | value
  · simp [fromInputs, dataEq, valuesEq, valueEq] at success
  simp [fromInputs, dataEq, valuesEq, valueEq] at success
  cases success
  exact encoded_lengths _ _ _

theorem fromInputs_claim (out : OODResult) (gamma kappa : K) (body : Bytes)
    (z : Fin 10 → K) (result : Encoded)
    (success : fromInputs out gamma kappa body z = some result) :
    result.claim = canonicalBytes result.value.claim := by
  rcases dataEq : fromSampled out gamma body with _ | data
  · simp [fromInputs, dataEq] at success
  rcases valuesEq : fields (body.map UInt8.toFin) with _ | values
  · simp [fromInputs, dataEq, valuesEq] at success
  rcases valueEq : correct ordinaryOps (wordOfValues values) gamma kappa
      (firstPoint data) (secondPoint data) z with _ | value
  · simp [fromInputs, dataEq, valuesEq, valueEq] at success
  simp [fromInputs, dataEq, valuesEq, valueEq] at success
  cases success
  rfl

theorem fromInputs_provenance (out : OODResult) (gamma kappa : K)
    (body : Bytes) (z : Fin 10 → K) (result : Encoded)
    (success : fromInputs out gamma kappa body z = some result) :
    ∃ values,
      fromSampled out gamma body = some result.data ∧
      fields (body.map UInt8.toFin) = some values ∧
      correct ordinaryOps (wordOfValues values) gamma kappa
          (firstPoint result.data) (secondPoint result.data) z = some result.value ∧
      result.description = descriptionBytes z result.value result.data ∧
      result.claim = canonicalBytes result.value.claim := by
  rcases dataEq : fromSampled out gamma body with _ | data
  · simp [fromInputs, dataEq] at success
  rcases valuesEq : fields (body.map UInt8.toFin) with _ | values
  · simp [fromInputs, dataEq, valuesEq] at success
  rcases valueEq : correct ordinaryOps (wordOfValues values) gamma kappa
      (firstPoint data) (secondPoint data) z with _ | value
  · simp [fromInputs, dataEq, valuesEq, valueEq] at success
  simp [fromInputs, dataEq, valuesEq, valueEq] at success
  cases success
  refine ⟨values, ?_, ?_, ?_, rfl, rfl⟩
  · simpa [encoded] using dataEq
  · simpa using valuesEq
  · simpa [encoded] using valueEq

theorem fromInputs_data_checked (out : OODResult) (gamma kappa : K)
    (body : Bytes) (z : Fin 10 → K) (result : Encoded)
    (success : fromInputs out gamma kappa body z = some result) :
    result.data.Checked := by
  obtain ⟨_, dataEq, _⟩ := fromInputs_provenance out gamma kappa body z result success
  exact fromSampled_checked out gamma body result.data dataEq

theorem fromInputs_data_gamma (out : OODResult) (gamma kappa : K)
    (body : Bytes) (z : Fin 10 → K) (result : Encoded)
    (success : fromInputs out gamma kappa body z = some result) :
    result.data.gamma = gamma := by
  obtain ⟨_, dataEq, _⟩ := fromInputs_provenance out gamma kappa body z result success
  exact fromSampled_gamma out gamma body result.data dataEq

#print axioms descriptionBytes_length
#print axioms encoded_lengths
#print axioms fromInputs_lengths
#print axioms fromInputs_claim
#print axioms fromInputs_provenance
#print axioms fromInputs_data_checked
#print axioms fromInputs_data_gamma

end
end AspisV8Completion.SameBodyFunctionalProducerSource
