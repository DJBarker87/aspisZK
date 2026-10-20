import CurrentFinishField
import CurrentWidePolynomialHornerListV10
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof

def currentRecordFieldLookup (bytes : Slice U8) (i : Usize) : Result E := do
  let value ← finishField bytes i
  ok (ofFinishE value)

theorem currentRecordFieldLookup_success_canonical
    (bytes : Slice U8) (i : Usize) (value : E)
    (h : currentRecordFieldLookup bytes i = .ok value) : CanonicalWide value := by
  unfold currentRecordFieldLookup at h
  cases hs : finishField bytes i with
  | fail e => simp only [hs, bind_tc_fail] at h; cases h
  | div => simp only [hs, bind_tc_div] at h; cases h
  | ok raw =>
    simp only [hs, bind_tc_ok] at h
    have he : ofFinishE raw = value := Result.ok.inj h
    have hc : CanonicalWide (ofFinishE raw) := finishField_success_canonical bytes i raw hs
    rw [← he]
    exact hc

def currentRecordFieldLookupNat (bytes : Slice U8) (i : Nat) : Result E :=
  if hi : i < 7 then
    currentRecordFieldLookup bytes (Usize.ofNatCore i (by scalar_tac))
  else .fail .panic

theorem currentRecordFieldLookupNat_success_canonical
    (bytes : Slice U8) (i : Nat) (value : E)
    (h : currentRecordFieldLookupNat bytes i = .ok value) : CanonicalWide value := by
  unfold currentRecordFieldLookupNat at h
  split at h
  · exact currentRecordFieldLookup_success_canonical bytes _ value h
  · simp at h

theorem current_horner_lookup7_actual_record_field_success
    (bytes : Slice U8) (multiplier out : E)
    (hmultiplier : CanonicalWide multiplier)
    (hrun : current_horner_lookup_run currentWideZero multiplier
      [6,5,4,3,2,1,0] (currentRecordFieldLookupNat bytes) = .ok out) :
    CanonicalWide out ∧ ∃ coefficients,
      (∀ c ∈ coefficients, CanonicalWide c) ∧
      List.Forall₂ (fun i c => currentRecordFieldLookupNat bytes i = .ok c)
        [6,5,4,3,2,1,0] coefficients ∧
      current_horner_run currentWideZero multiplier coefficients = .ok out ∧
      decodeWide out = horner_value 0 (decodeWide multiplier)
        (coefficients.map decodeWide) := by
  apply current_horner_lookup7_success
  · exact hmultiplier
  · intro i c hc
    exact currentRecordFieldLookupNat_success_canonical bytes i c hc
  · exact hrun

#print axioms currentRecordFieldLookup_success_canonical
#print axioms currentRecordFieldLookupNat_success_canonical
#print axioms current_horner_lookup7_actual_record_field_success
end AspisR1CurrentWide.Proof
