import S9PointPartsFoldValuesV1
import S9StoredZeroFourSameAlphaV1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1S9SevenSourceRowValuesV1
open AspisR1S9FactorTableSemanticsV1 (Table)
open AspisR1S9PointRowDualFoldModelV1 (rawRow)
open AspisR1S9SharedScalarModelValuesV1 (embedQ)
open AspisR1S9KappaFinSevenV1 (W partAt)
open AspisR1S9ActualFinalSumV1 (A)
open AspisR1S9NativeWideDecodedArithmeticV1 (decode)
open AspisR1S9ActiveOriginalCoefficientsV1 (Q)
open AspisR1S9ActualPairOldCarrierScalarV1 (toHelperQ)
open AspisR1S9StoredZeroFourSameAlphaV1 (input)
abbrev E := AspisWideTower.WideExact
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

/-- Exact source order: inactive, three statement rows, private, two circle
rows. The point table and private seeds are supplied by the SAME constructor. -/
def rows (model : Table) (q0 q1 : Q) (i : Fin 7) : Fin 1024 → E :=
  if i.val=0 then AspisR1S9TwoDualSourceBaseV1.inactiveRow
  else if i.val=1 then fun j => embedQ (rawRow model 0 j)
  else if i.val=2 then fun j => embedQ (rawRow model 1 j)
  else if i.val=3 then fun j => embedQ (rawRow model 2 j)
  else if i.val=4 then AspisR1S9TwoDualSourcePrivateV1.privateRow
    (AspisR1S9ActualPairHelperOriginalCoefficientsV1.Seed (toHelperQ q0))
    (AspisR1S9ActualPairHelperOriginalCoefficientsV1.Seed (toHelperQ q1))
  else if i.val=5 then fun j => embedQ (rawRow model 3 j)
  else fun j => embedQ (rawRow model 4 j)

private theorem read_zero (parts : A) (i : Fin 7) (hi : i.val=0) :
    partAt parts i=AspisR1S9InactiveFinalZeroCellV1.cell0 parts :=
  AspisR1S9KappaFinReadConsumerV1.partAt_eq_atN parts i 0#usize (by decide)
    (by change 0=i.val;exact hi.symm)
private theorem read_four (parts : A) (i : Fin 7) (hi : i.val=4) :
    partAt parts i=AspisR1S9ActiveFourValueStepV1.cell4 parts :=
  AspisR1S9KappaFinReadConsumerV1.partAt_eq_atN parts i 4#usize (by decide)
    (by change 4=i.val;exact hi.symm)

/-- Assemble only already-derived outputs on ONE supplied array and one
alpha pair. No independently selected input stream or desired source result. -/
theorem all_values (self : AspisR1S9ProductionPairCutV1.weights.Weights)
    (model : Table) (a0 a1 : W) (f : Slice U8) (parts : A)
    (hz : AspisR1S9StoredZeroFourSameAlphaV1.Meanings self f parts a0 a1)
    (hp : AspisR1S9PointPartsFoldValuesV1.FivePointFolds model (decode a0) (decode a1) f parts) :
    ∃ q0 q1 : Q,
      Array.index_usize self.extra 0#usize=.ok q0 ∧
      Array.index_usize self.extra 1#usize=.ok q1 ∧
      ∀ i : Fin 7,decode (partAt parts i)=AspisR1.RoundPairing.dot (input f)
        (AspisR1.RoundPairing.dualFold (decode a1)
          (AspisR1.RoundPairing.dualFold (decode a0) (rows model q0 q1 i))) := by
  obtain ⟨q0,q1,hq0,hq1,h0,h4⟩ := hz
  obtain ⟨h1,h2,h3,h5,h6⟩ := hp
  refine ⟨q0,q1,hq0,hq1,?_⟩
  intro i
  by_cases hi0 : i.val=0
  · rw [rows,if_pos hi0]
    exact (congrArg decode (read_zero parts i hi0)).trans h0
  by_cases hi1 : i.val=1
  · simpa only [rows,hi0,hi1,if_false,if_true,
      AspisR1S9PointCommonInputFoldV1.pointFoldValue,input] using h1 i hi1
  by_cases hi2 : i.val=2
  · simpa only [rows,hi0,hi1,hi2,if_false,if_true,
      AspisR1S9PointCommonInputFoldV1.pointFoldValue,input] using h2 i hi2
  by_cases hi3 : i.val=3
  · simpa only [rows,hi0,hi1,hi2,hi3,if_false,if_true,
      AspisR1S9PointCommonInputFoldV1.pointFoldValue,input] using h3 i hi3
  by_cases hi4 : i.val=4
  · simp only [rows,hi0,hi1,hi2,hi3,hi4,if_false,if_true]
    exact (congrArg decode (read_four parts i hi4)).trans h4
  by_cases hi5 : i.val=5
  · simpa only [rows,hi0,hi1,hi2,hi3,hi4,hi5,if_false,if_true,
      AspisR1S9PointCommonInputFoldV1.pointFoldValue,input] using h5 i hi5
  have hi6 : i.val=6 := by have := i.isLt;omega
  simpa only [rows,hi0,hi1,hi2,hi3,hi4,hi5,if_false,if_true,
    AspisR1S9PointCommonInputFoldV1.pointFoldValue,input] using h6 i hi6

#print axioms all_values
end AspisR1S9SevenSourceRowValuesV1
end
