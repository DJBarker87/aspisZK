import S9PointCommonInputFoldV1
import S9KappaFinReadConsumerV1
import S9RegularPhaseModelPreludeV1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1S9PointPartsFoldValuesV1
open AspisR1S9FactorTableSemanticsV1 (Table)
open AspisR1S9PointRowDualFoldModelV1 (E)
open AspisR1S9ActualFinalSumV1 (A)
open AspisR1S9KappaFinSevenV1 (W partAt)
open AspisR1S9KappaFinReadConsumerV1 (partAt_eq_atN)
open AspisR1S9RegularPhaseConstructorModelV1 (Means)
open AspisR1S9PointCommonInputFoldV1 (pointFoldValue)
open AspisR1S9NativeWideDecodedArithmeticV1 (decode)
open AspisR1S9NativeDecodedScalarProductV1 (decodeNative)

private theorem decode_native_alias (x : W) : decode x=decodeNative x := rfl

/-- One actual part read, on the supplied array and the supplied model. -/
theorem means_partAt_fold (model : Table) (a0 a1 : E) (f : Slice U8)
    (parts : A) (i : Fin 7) (j : Usize) (hj : j.val<7) (hji : j.val=i.val)
    (row : Nat) (h : Means model a0 a1 f parts j hj row) :
    decode (partAt parts i)=pointFoldValue model a0 a1 f row := by
  have hr := partAt_eq_atN parts i j hj hji
  have hm : decodeNative (AspisR1S9FactorArrayEntryV1.atN parts j hj)=
      AspisR1S9SharedHighConstructorModelV1.rowValue model a0 a1 f row := h
  have hv := (congrArg decodeNative hr).trans hm
  have hd := AspisR1S9PointCommonInputFoldV1.rowValue_eq_common_input_fold model a0 a1 f row
  exact (decode_native_alias (partAt parts i)).trans (hv.trans hd)

/-- Output equations only; no desired meanings are premises of this predicate. -/
def FivePointFolds (model : Table) (a0 a1 : E) (f : Slice U8) (parts : A) : Prop :=
  (∀ i : Fin 7,i.val=1 → decode (partAt parts i)=pointFoldValue model a0 a1 f 0) ∧
  (∀ i : Fin 7,i.val=2 → decode (partAt parts i)=pointFoldValue model a0 a1 f 1) ∧
  (∀ i : Fin 7,i.val=3 → decode (partAt parts i)=pointFoldValue model a0 a1 f 2) ∧
  (∀ i : Fin 7,i.val=5 → decode (partAt parts i)=pointFoldValue model a0 a1 f 3) ∧
  (∀ i : Fin 7,i.val=6 → decode (partAt parts i)=pointFoldValue model a0 a1 f 4)

/-- Exactly the five Means already carried by ONE accepted PointModel.
No source, canonicality or extra constructor/model premise is introduced. -/
theorem five_means_folds (model : Table) (a0 a1 : E) (f : Slice U8) (parts : A)
    (hj1 : (1#usize).val<7) (hj2 : (2#usize).val<7) (hj3 : (3#usize).val<7)
    (hj5 : (5#usize).val<7) (hj6 : (6#usize).val<7)
    (h1 : Means model a0 a1 f parts 1#usize hj1 0)
    (h2 : Means model a0 a1 f parts 2#usize hj2 1)
    (h3 : Means model a0 a1 f parts 3#usize hj3 2)
    (h5 : Means model a0 a1 f parts 5#usize hj5 3)
    (h6 : Means model a0 a1 f parts 6#usize hj6 4) :
    FivePointFolds model a0 a1 f parts := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i hi
    exact means_partAt_fold model a0 a1 f parts i 1#usize hj1 (by change 1=i.val;exact hi.symm) 0 h1
  · intro i hi
    exact means_partAt_fold model a0 a1 f parts i 2#usize hj2 (by change 2=i.val;exact hi.symm) 1 h2
  · intro i hi
    exact means_partAt_fold model a0 a1 f parts i 3#usize hj3 (by change 3=i.val;exact hi.symm) 2 h3
  · intro i hi
    exact means_partAt_fold model a0 a1 f parts i 5#usize hj5 (by change 5=i.val;exact hi.symm) 3 h5
  · intro i hi
    exact means_partAt_fold model a0 a1 f parts i 6#usize hj6 (by change 6=i.val;exact hi.symm) 4 h6
#print axioms means_partAt_fold
#print axioms five_means_folds
end AspisR1S9PointPartsFoldValuesV1
end
