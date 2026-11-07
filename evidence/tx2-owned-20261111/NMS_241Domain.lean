import NMN_064
import NLW_StartScope
import AdapterRwRanges
set_option autoImplicit false
noncomputable section
namespace NMS_241Domain
open Aeneas Aeneas.Std AdapterRw
/-- Discharges the064 numeric clauses from the241 source operations, at the
SAME byte slices. Checkpoint extent and Root0 are deliberately retained as
241 own-input clauses, not inferred from authenticity or hash equality.
This local cut lemma is NOT a row root. -/
theorem from_entered {X : Type} (digest : VTop_Stages.aspis_core.digest.Digest32 X)
 (hash : X) (account proof checkpoint : Slice U8) (publicBytes : Array U8 1880#usize)
 (length end_ : Usize)
 (validatedLength : length = 57607#usize)
 (checked : Usize.checked_add 688#usize length = some end_)
 (guard : (Slice.len account != end_) = false)
 (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  account {start := 688#usize, «end» := end_} = .ok proof)
 (checkpointExtent : checkpoint.val.length = 1768)
 (root0 : NLP_InputDomain.Root0 checkpoint proof) :
 NMN_064.Domain (NLW_Full064.Args.mk digest publicBytes.to_slice proof checkpoint hash) := by
 have sum := NLM_CheckedAddFacts.success 688#usize length end_ checked
 rw [validatedLength] at sum
 have endValue : end_.val = 58295 := by exact sum
 have guardValue := congrArg (fun z : Usize => z.val)
  (NLM_CheckedAddFacts.guard_eq account end_ guard)
 have accountLength : account.val.length = end_.val := by
  simpa only [Slice.len_val] using guardValue
 have suffix := AspisR1.AdapterRw.Ranges.suffix_exact account proof 688#usize end_
  (by change 688 ≤ end_.val; omega) accountLength range
 constructor
 · have extent := suffix.1
   rw [endValue] at extent
   exact extent
 · exact checkpointExtent
 · have extent := NLE_Length.public_extent publicBytes
   exact Nat.le_of_eq extent
 · exact root0
#print from_entered
#print axioms from_entered
end NMS_241Domain
