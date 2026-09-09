import PackedLimbCollect
import AspisFormal.Pool.V7PackedFibreDecoder
import CanonicalRelationInput

/-! Literal 621-byte packed query record projection. The reused V7 bit
decoder describes contiguous little-endian 31-bit limbs; the optimized
four-u64 shift/or implementation remains a distinct machine refinement.
No Merkle or global received-word correspondence is assumed or concluded. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 30000
namespace AspisV8.PackedQueryRecord
noncomputable section
open AspisPool.V7MerkleQueryGrammar AspisPool.V7PackedLimbDecoder
open AspisPool.V7PackedFibreIndices AspisPool.V7PackedC1Entry
open AspisPool.V7PackedC2Entry AspisPool.V7CanonicalQM31
open AspisPool.V7PackedFibreTowerBridge AspisV5ComponentCQM31TowerExact
open scoped BigOperators
abbrev K := QM31Exact

def c1Bytes (record : List Byte) : C1Value := fun i=>record.getD i.val 0
def c2Bytes (record : List Byte) : C2Value := fun i=>record.getD (403+i.val) 0
def saltBytes (record : List Byte) : Salt32 := fun i=>record.getD (589+i.val) 0
def zeroLimb : CanonicalM31 := ⟨0,by decide⟩

structure Decoded where
  c1 : Fin 104 → CanonicalM31
  c2 : Fin 48 → CanonicalM31
  salt : Salt32

def assemble (record : List Byte) (first second : List CanonicalM31) : Decoded :=
  ⟨fun i=>first.getD i.val zeroLimb, fun i=>second.getD i.val zeroLimb, saltBytes record⟩

def parse (record : List Byte) : Option Decoded :=
  if record.length≠621 then none else
    Option.bind (PackedLimbCollect.collect m31Modulus (c1PackedLimbNat (c1Bytes record)))
      (fun first=>Option.bind
        (PackedLimbCollect.collect m31Modulus (c2PackedLimbNat (c2Bytes record)))
        (fun second=>some (assemble record first second)))

theorem malformed_length (record : List Byte) (bad : record.length≠621) :
    parse record=none := by simp only [parse,if_pos bad]

theorem success_exact (record : List Byte) (decoded : Decoded)
    (success : parse record=some decoded) :
    record.length=621 ∧
      (∀ i, c1PackedLimbNat (c1Bytes record) i=(decoded.c1 i).val) ∧
      (∀ i, c2PackedLimbNat (c2Bytes record) i=(decoded.c2 i).val) ∧
      decoded.salt=saltBytes record := by
  unfold parse at success
  split at success
  · contradiction
  · rename_i length
    have hlen : record.length=621 := not_ne_iff.mp length
    cases h1 : PackedLimbCollect.collect m31Modulus (c1PackedLimbNat (c1Bytes record)) with
    | none => simp only [h1,Option.bind_none] at success; cases success
    | some first =>
      cases h2 : PackedLimbCollect.collect m31Modulus (c2PackedLimbNat (c2Bytes record)) with
      | none => simp only [h1,h2,Option.bind_some,Option.bind_none] at success; cases success
      | some second =>
        have same : assemble record first second=decoded := by
          simpa only [h1,h2,Option.bind_some,Option.some.injEq] using success
        subst decoded
        exact ⟨hlen,(PackedLimbCollect.success_raw _ first zeroLimb h1).2,
          (PackedLimbCollect.success_raw _ second zeroLimb h2).2,rfl⟩

theorem c1_byte_in_bounds (record : List Byte) (decoded : Decoded)
    (success : parse record=some decoded) (i : Fin 403) :
    i.val<record.length := by
  rw [(success_exact record decoded success).1]
  omega
theorem c2_byte_in_bounds (record : List Byte) (decoded : Decoded)
    (success : parse record=some decoded) (i : Fin 186) :
    403+i.val<record.length := by
  rw [(success_exact record decoded success).1]
  omega
theorem salt_byte_in_bounds (record : List Byte) (decoded : Decoded)
    (success : parse record=some decoded) (i : Fin 32) :
    589+i.val<record.length := by
  rw [(success_exact record decoded success).1]
  omega

theorem noncanonical_c1 (record : List Byte) (i : Fin 104)
    (high : m31Modulus≤c1PackedLimbNat (c1Bytes record) i) : parse record=none := by
  cases result : parse record with
  | none => rfl
  | some decoded =>
    have exactValue := (success_exact record decoded result).2.1 i
    have bound := (decoded.c1 i).isLt
    rw [←exactValue] at bound
    exact False.elim ((not_lt_of_ge high) bound)
theorem noncanonical_c2 (record : List Byte) (i : Fin 48)
    (high : m31Modulus≤c2PackedLimbNat (c2Bytes record) i) : parse record=none := by
  cases result : parse record with
  | none => rfl
  | some decoded =>
    have exactValue := (success_exact record decoded result).2.2.1 i
    have bound := (decoded.c2 i).isLt
    rw [←exactValue] at bound
    exact False.elim ((not_lt_of_ge high) bound)

theorem c1_limb_decodes (record : List Byte) (decoded : Decoded)
    (success : parse record=some decoded) (i : Fin 104) :
    decodeC1PackedLimb (c1Bytes record) i=some (decoded.c1 i) := by
  have exactValue := (success_exact record decoded success).2.1 i
  unfold decodeC1PackedLimb
  rw [exactValue,dif_pos (decoded.c1 i).isLt]
theorem c2_limb_decodes (record : List Byte) (decoded : Decoded)
    (success : parse record=some decoded) (i : Fin 48) :
    decodeC2PackedLimb (c2Bytes record) i=some (decoded.c2 i) := by
  have exactValue := (success_exact record decoded success).2.2.1 i
  unfold decodeC2PackedLimb
  rw [exactValue,dif_pos (decoded.c2 i).isLt]

def baseValue (decoded : Decoded) (slot : Fin 4) (column : Fin 26) : M31Exact :=
  canonicalM31ToExact (decoded.c1 (c1LimbIndex slot column))
def helperLimbs (decoded : Decoded) (helper : Fin 3) (slot : Fin 4) : CanonicalQM31 :=
  ⟨decoded.c2 (c2LimbIndex helper slot 0),decoded.c2 (c2LimbIndex helper slot 1),
    decoded.c2 (c2LimbIndex helper slot 2),decoded.c2 (c2LimbIndex helper slot 3)⟩
def helperValue (decoded : Decoded) (helper : Fin 3) (slot : Fin 4) : K :=
  canonicalQM31ToExact (helperLimbs decoded helper slot)

theorem c1_entry (record : List Byte) (decoded : Decoded)
    (success : parse record=some decoded) (slot : Fin 4) (column : Fin 26) :
    decodeC1EntryExact (c1Bytes record) slot column=some (baseValue decoded slot column) := by
  unfold decodeC1EntryExact decodeC1Entry
  rw [c1_limb_decodes record decoded success]
  rfl
theorem c2_entry (record : List Byte) (decoded : Decoded)
    (success : parse record=some decoded) (helper : Fin 3) (slot : Fin 4) :
    decodeC2EntryExact (c2Bytes record) helper slot=some (helperValue decoded helper slot) := by
  have assembled : decodeC2Entry (c2Bytes record) helper slot=
      some (helperLimbs decoded helper slot) :=
    assembleC2Entry_of_eq_some _ _ _ _ _ _ _ _
      (c2_limb_decodes record decoded success (c2LimbIndex helper slot 0))
      (c2_limb_decodes record decoded success (c2LimbIndex helper slot 1))
      (c2_limb_decodes record decoded success (c2LimbIndex helper slot 2))
      (c2_limb_decodes record decoded success (c2LimbIndex helper slot 3))
  exact decoded_c2_exact_has_deployed_tower_order (c2Bytes record) helper slot
    _ _ _ _ assembled

/-- The field-level form of the source's 26 mixed terms plus H/G/D.
This is not yet the u64 delayed-reduction implementation. -/
def combined (gamma : K) (decoded : Decoded) (slot : Fin 4) : K :=
  (∑ column : Fin 26, gamma^column.val*algebraMap M31Exact K (baseValue decoded slot column))+
  gamma^26*helperValue decoded 0 slot+gamma^27*helperValue decoded 1 slot+
  gamma^28*helperValue decoded 2 slot

def laneValue (decoded : Decoded) (slot : Fin 4) (lane : Fin 29) : K :=
  if h : lane.val<26 then algebraMap M31Exact K (baseValue decoded slot ⟨lane.val,h⟩)
  else helperValue decoded ⟨lane.val-26,by omega⟩ slot

theorem lane_base (decoded : Decoded) (slot : Fin 4) (column : Fin 26) :
    laneValue decoded slot (Fin.castAdd 3 column)=
      algebraMap M31Exact K (baseValue decoded slot column) := by
  simp only [laneValue,Fin.val_castAdd,dif_pos column.isLt]
theorem lane_helper (decoded : Decoded) (slot : Fin 4) (helper : Fin 3) :
    laneValue decoded slot (Fin.natAdd 26 helper)=helperValue decoded helper slot := by
  have high : ¬26+helper.val<26 := by omega
  simp only [laneValue,Fin.val_natAdd,dif_neg high,Nat.add_sub_cancel_left]

theorem combined_eq_scalar_power (gamma : K) (decoded : Decoded) (slot : Fin 4) :
    combined gamma decoded slot=∑ lane : Fin 29, gamma^lane.val*laneValue decoded slot lane := by
  rw [Fin.sum_univ_add (a:=26) (b:=3)]
  simp only [lane_base,lane_helper,Fin.val_castAdd,Fin.val_natAdd]
  rw [Fin.sum_univ_three]
  simp only [Fin.val_zero,Fin.val_one,Fin.val_two]
  unfold combined
  ring

/-- Total raw-byte interpretation used only under successful canonical
parsing below. This totalization does not turn a parse failure into success. -/
def rawBase (record : List Byte) (slot : Fin 4) (column : Fin 26) : M31Exact :=
  c1PackedLimbNat (c1Bytes record) (c1LimbIndex slot column)
def rawHelper (record : List Byte) (helper : Fin 3) (slot : Fin 4) : K :=
  let raw := fun basis=>c2PackedLimbNat (c2Bytes record) (c2LimbIndex helper slot basis)
  ⟨⟨(raw 0 : M31Exact),(raw 1 : M31Exact)⟩,
    ⟨(raw 2 : M31Exact),(raw 3 : M31Exact)⟩⟩
def rawLane (record : List Byte) (slot : Fin 4) (lane : Fin 29) : K :=
  if h : lane.val<26 then algebraMap M31Exact K (rawBase record slot ⟨lane.val,h⟩)
  else rawHelper record ⟨lane.val-26,by omega⟩ slot
def rawCombined (gamma : K) (record : List Byte) (slot : Fin 4) : K :=
  ∑ lane : Fin 29, gamma^lane.val*rawLane record slot lane

theorem baseValue_eq_raw (record : List Byte) (decoded : Decoded)
    (success : parse record=some decoded) (slot : Fin 4) (column : Fin 26) :
    baseValue decoded slot column=rawBase record slot column := by
  unfold baseValue rawBase canonicalM31ToExact
  rw [(success_exact record decoded success).2.1]
theorem helperValue_eq_raw (record : List Byte) (decoded : Decoded)
    (success : parse record=some decoded) (helper : Fin 3) (slot : Fin 4) :
    helperValue decoded helper slot=rawHelper record helper slot := by
  unfold helperValue helperLimbs canonicalQM31ToExact canonicalM31ToExact rawHelper
  simp only [(success_exact record decoded success).2.2.1]
theorem laneValue_eq_raw (record : List Byte) (decoded : Decoded)
    (success : parse record=some decoded) (slot : Fin 4) (lane : Fin 29) :
    laneValue decoded slot lane=rawLane record slot lane := by
  unfold laneValue rawLane
  split
  · rw [baseValue_eq_raw record decoded success]
  · rw [helperValue_eq_raw record decoded success]
theorem combined_eq_raw (record : List Byte) (decoded : Decoded)
    (success : parse record=some decoded) (gamma : K) (slot : Fin 4) :
    combined gamma decoded slot=rawCombined gamma record slot := by
  rw [combined_eq_scalar_power]
  simp only [laneValue_eq_raw record decoded success,rawCombined]

def bodyRecord (body : List Byte) (query : Fin 22) : List Byte :=
  List.ofFn fun byte : Fin 621=>body.getD (11228+621*query.val+byte.val) 0

theorem bodyRecord_length (body : List Byte) (query : Fin 22) :
    (bodyRecord body query).length=621 := by simp only [bodyRecord,List.length_ofFn]

theorem bodyRecord_byte (body : List Byte) (query : Fin 22) (byte : Fin 621) :
    (bodyRecord body query).getD byte.val 0=
      body.getD (11228+621*query.val+byte.val) 0 := by
  unfold bodyRecord
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using byte.isLt)]
  exact List.getElem_ofFn _

theorem body_record_in_bounds (body : List Byte) (values : List K)
    (success : CanonicalRelationInput.parseFixed body=some values)
    (query : Fin 22) (byte : Fin 621) :
    11228+621*query.val+byte.val<body.length := by
  have good := (CanonicalRelationInput.parse_success body values success).1
  unfold CanonicalRelationInput.badLength at good
  have hq:=query.isLt
  have hb:=byte.isLt
  omega

theorem bodyRecord_byte_exact (body : List Byte) (values : List K)
    (success : CanonicalRelationInput.parseFixed body=some values)
    (query : Fin 22) (byte : Fin 621) :
    (bodyRecord body query).getD byte.val 0=
      body[11228+621*query.val+byte.val]'(body_record_in_bounds body values success query byte) := by
  rw [bodyRecord_byte]
  exact List.getD_eq_getElem _ _ (body_record_in_bounds body values success query byte)

#print axioms success_exact
#print axioms c1_byte_in_bounds
#print axioms c2_byte_in_bounds
#print axioms salt_byte_in_bounds
#print axioms noncanonical_c1
#print axioms noncanonical_c2
#print axioms c1_entry
#print axioms c2_entry
#print axioms combined_eq_scalar_power
#print axioms combined_eq_raw
#print axioms bodyRecord_length
#print axioms body_record_in_bounds
#print axioms bodyRecord_byte_exact
end
end AspisV8.PackedQueryRecord
