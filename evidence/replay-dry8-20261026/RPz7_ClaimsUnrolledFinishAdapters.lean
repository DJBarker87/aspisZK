import RPz7_ClaimsUnrolledFinish
/-! Nominal carrier transport for the actual source callees installed in
ClaimsUnrolledFinish. Full raw field words and all error/fail/div outcomes,
with no canonical-input restriction or native memory/effect claim. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.ClaimsUnrolledFinish
open Aeneas Aeneas.Std Result

theorem error_back (e : MainError) : toMainError (fromMainError e) = e := by
  cases e <;> rfl

theorem qm_back (q : MainQM) : toMainQM (fromMainQM q) = q := by
  cases q with
  | mk c0 c1 => cases c0; cases c1; rfl

theorem array_back {n : Usize} (a : Array MainQM n) :
    toMainArray (fromMainArray a) = a := by
  apply Subtype.ext
  change (a.val.map fromMainQM).map toMainQM = a.val
  rw [List.map_map]
  simp only [Function.comp_def,qm_back,List.map_id_fun']
  rfl

theorem prefix_back (p : MainPrefix) : toMainPrefix (fromMainPrefix p) = p := by
  cases p
  rfl

def toMainDecoded {n : Usize} :
    Result (core.result.Result (Array ParentQM n) ParentError) →
      Result (core.result.Result (Array MainQM n) MainError)
  | .ok (.Ok a) => .ok (.Ok (toMainArray a))
  | .ok (.Err e) => .ok (.Err (toMainError e))
  | .fail e => .fail e
  | .div => .div

/-- Exact actual indexed source decoder at the SAME record/offset, all N
and all outcomes. This discharges the nominal adapter, not native Std/ABI. -/
theorem decode_exact (n : Usize) (r : AspisR1ClaimsUnrolledParent.r1_wire.ValidatedRecord)
    (offset : Usize) :
    toMainDecoded (sourceDecode n r offset) =
      AspisS1ExtractedRoundChildren.decodeMain n (toMainRecord r) offset := by
  cases h : AspisS1ExtractedRoundChildren.decodeMain n (toMainRecord r) offset with
  | fail e => simp [sourceDecode,toMainDecoded,h]
  | div => simp [sourceDecode,toMainDecoded,h]
  | ok result => cases result <;> simp [sourceDecode,toMainDecoded,h,array_back,error_back]

def toMainRecordStatus :
    Result (core.result.Result AspisR1ClaimsUnrolledParent.r1_wire.ValidatedRecord ParentError) →
      Result (core.result.Result MainRecord MainError)
  | .ok (.Ok r) => .ok (.Ok (toMainRecord r))
  | .ok (.Err e) => .ok (.Err (toMainError e))
  | .fail e => .fail e
  | .div => .div

/-- Exact source getter after the full prefix carrier roundtrip. Every byte
of the original record array and root remains the same. -/
theorem getter_exact (pre : MainPrefix) (row : U8) :
    toMainRecordStatus (sourceRecord (fromMainPrefix pre) row) =
      AspisR1PublicPreparation.r1_wire.Prefix.validated_record pre row := by
  unfold sourceRecord
  rw [prefix_back]
  cases h : AspisR1PublicPreparation.r1_wire.Prefix.validated_record pre row with
  | fail e => rfl
  | div => rfl
  | ok result =>
    cases result with
    | Err e => simp [toMainRecordStatus,error_back]
    | Ok r => cases r; rfl

#print axioms decode_exact
#print axioms getter_exact
#print axioms claims_value
#print axioms finish_claims
#print StdCalls
#print install
#print external
#print finish_claims
end AspisR1.ClaimsUnrolledFinish
end
