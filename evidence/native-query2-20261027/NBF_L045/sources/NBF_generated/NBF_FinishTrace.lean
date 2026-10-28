import NBF_FirstRows
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBF_FinishTrace
open AspisR1 AspisR1Stage2
abbrev Q := NBF_RowInstall.Q
abbrev Row := NBF_Frame.Row
noncomputable def value (row : Row) : Q := Port3_FlushInstall.fromMutable
 (S8Kani2FinishReferenceJoin.toFinish (S8OwnedP6Finish.modelValue row))
/-- Prefix invariant for single native finish writes, retaining the SAME raw
source and original destination length. -/
def Prefix (raw : NBF_Frame.Raw) (out : Slice Q) (cursor : Nat) : Prop :=
 ∀ j, j<cursor → out.val[j]?=(raw.val[j]?).map value

theorem initial (raw : NBF_Frame.Raw) (out : Slice Q) : Prefix raw out 0 := by
 intro j impossible;omega

theorem step (raw : NBF_Frame.Raw) (out : Slice Q) (i : Usize) (row : Row)
 (inRange : i.val<out.val.length) (correct : Prefix raw out i.val)
 (read : raw.val[i.val]?=some row) :
 Prefix raw (out.set i (value row)) (i.val+1) := by
 intro j bound
 change (out.val.set i.val (value row))[j]?=_
 by_cases same : j=i.val
 · subst j
   rw [List.getElem?_set_self inRange,read]
   rfl
 · rw [List.getElem?_set_ne (Ne.symm same)]
   exact correct j (by omega)

theorem complete (b : verifier.BatchedWeights) (old out : Slice Q)
 (raw64 : b.raw.val.length=64) (old64 : old.val.length=64) (out64 : out.val.length=64)
 (correct : Prefix b.raw out 64) : Port3_FlushInstall.flush b old=ok out := by
 obtain ⟨expected,run,len,contents,canonical⟩ := NBB_Finish.source b old raw64 old64
 have same : expected=out := by
   apply Subtype.ext
   apply List.ext_getElem?
   intro j
   by_cases bound : j<64
   · rw [contents,List.getElem?_map,List.take_of_length_le (by omega)]
     exact (correct j bound).symm
   · rw [List.getElem?_eq_none (by omega),List.getElem?_eq_none (by omega)]
 exact run.trans (congrArg Result.ok same)
#print axioms initial
#print axioms step
#print axioms complete
end NBF_FinishTrace
