import SelectedInitialOutputsSourcePolynomial
import SelectedAppendAfterstate
import BooleanSuffixSourceAlgebra

/-! Chronological sources for the final eight digest and two scalar outputs. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
set_option maxRecDepth 10000

namespace AspisV8Completion.SelectedPublicOutputsSourcePolynomial
open scoped BigOperators
open Polynomial
open AspisFormal.HashMerkleModel
open AspisV5ComponentCQM31TowerExact
open AspisV8.PositivePackBinding
open AspisV8.SelectedSemanticRows
open AspisV8.SelectedSemanticLaneAggregation
open AspisV8.SelectedAppendAfterstate
open AspisV8Completion.CausalSourcePolynomialTrace
open AspisV8Completion.SelectedRangeLaneCoordinateSlice
open AspisV8Completion.BooleanSuffixSourceConstructor
open AspisV8Completion.BooleanSuffixSourceAlgebra
open AspisV8Completion.SelectedValueAuxiliarySourcePolynomial
open AspisV8Completion.SelectedRecompositionRustShaped
open AspisV8Completion.SelectedRecompositionSourcePolynomial
open AspisV8Completion.SelectedInitialOutputsSourcePolynomial

abbrev K := QM31Exact
abbrev F := M31Exact

def rowTable (target : Nat) : Fin 1024 → K :=
  indicatorTable (fun row => row = target)

def rowValue (target : Nat) (point : Fin 10 → K) : K :=
  mleValue (rowTable target) point

noncomputable def rowSlice (target : Nat) (fixed : Fin 10 → K)
    (round : Fin 10) : K[X] := mleSlice (rowTable target) fixed round

def bindingValue (table : BaseTable) (point : Fin 10 → K)
    (row column : Nat) (expected : F) : K :=
  rowValue row point * (openValue table point column - liftBase expected)

noncomputable def bindingSlice (table : BaseTable) (fixed : Fin 10 → K)
    (round : Fin 10) (row column : Nat) (expected : F) : K[X] :=
  rowSlice row fixed round * (openSlice table fixed round column - C (liftBase expected))

theorem bindingSlice_degree (table : BaseTable) (fixed : Fin 10 → K)
    (round : Fin 10) (row column : Nat) (expected : F) :
    (bindingSlice table fixed round row column expected).natDegree ≤ 2 := by
  unfold bindingSlice rowSlice
  apply natDegree_mul_le.trans
  exact (Nat.add_le_add (mleSlice_degree _ _ _)
    ((natDegree_sub_le _ _).trans (max_le (openingSlice_degree _ _ _) (by simp)))).trans
      (by omega)

theorem bindingSlice_eval_at (table : BaseTable) (fixed : Fin 10 → K)
    (round : Fin 10) (row column : Nat) (expected : F) (x : K) :
    (bindingSlice table fixed round row column expected).eval x =
      bindingValue table (replaceCoordinate fixed round x) row column expected := by
  simp only [bindingSlice, bindingValue, rowSlice, rowValue, eval_mul, eval_sub,
    eval_C, mleSlice_eval_at, openSlice_eval_at]

theorem rowValue_boolean (target : Nat) (row : Fin 1024) :
    rowValue target (booleanTracePoint row) = if row.val = target then 1 else 0 :=
  indicator_boolean (fun value => value = target) row

theorem bindingValue_boolean (table : BaseTable) (target column : Nat)
    (expected : F) (row : Fin 1024) :
    bindingValue table (booleanTracePoint row) target column expected =
      liftBase (gate (row.val = target) (table row.val column - expected)) := by
  unfold bindingValue gate
  rw [rowValue_boolean, openValue_boolean]
  by_cases active : row.val = target
  · simp [active, liftBase_sub]
  · simp [active, liftBase_zero]

def appendTermValue (pub : Public) (table : BaseTable) (point : Fin 10 → K)
    (limb : Fin 8) (level : Fin 20) : K :=
  if pub.appendIndex.testBit level.val then
    bindingValue table point (16 * (34 + level.val) + 12) limb.val
      (pub.frontier level limb)
  else bindingValue table point (16 * (34 + level.val)) (8 + limb.val)
    (emptyRoot level limb + if limb.val = 7 then NODE_TWEAK else 0)

noncomputable def appendTermSlice (pub : Public) (table : BaseTable)
    (fixed : Fin 10 → K) (round : Fin 10) (limb : Fin 8)
    (level : Fin 20) : K[X] :=
  if pub.appendIndex.testBit level.val then
    bindingSlice table fixed round (16 * (34 + level.val) + 12) limb.val
      (pub.frontier level limb)
  else bindingSlice table fixed round (16 * (34 + level.val)) (8 + limb.val)
    (emptyRoot level limb + if limb.val = 7 then NODE_TWEAK else 0)

def carryValue (pub : Public) (table : BaseTable) (point : Fin 10 → K)
    (limb : Fin 8) : K :=
  if within : carryIndex pub.appendIndex < 20 then
    bindingValue table point
      (16 * (33 + carryIndex pub.appendIndex) + 11)
      limb.val
      (pub.nextFrontier ⟨carryIndex pub.appendIndex, within⟩ limb)
  else 0

noncomputable def carrySlice (pub : Public) (table : BaseTable)
    (fixed : Fin 10 → K) (round : Fin 10) (limb : Fin 8) : K[X] :=
  if within : carryIndex pub.appendIndex < 20 then
    bindingSlice table fixed round
      (16 * (33 + carryIndex pub.appendIndex) + 11)
      limb.val
      (pub.nextFrontier ⟨carryIndex pub.appendIndex, within⟩ limb)
  else 0

def digestHeadValue (pub : Public) (table : BaseTable) (point : Fin 10 → K)
    (limb : Fin 8) : K :=
  bindingValue table point 907 limb.val (pub.anchor limb) +
  bindingValue table point 427 limb.val (pub.nullifier limb) +
  bindingValue table point 475 limb.val (pub.commitments 0 limb) +
  bindingValue table point 523 limb.val (pub.commitments 1 limb)

noncomputable def digestHeadSlice (pub : Public) (table : BaseTable)
    (fixed : Fin 10 → K) (round : Fin 10) (limb : Fin 8) : K[X] :=
  bindingSlice table fixed round 907 limb.val (pub.anchor limb) +
  bindingSlice table fixed round 427 limb.val (pub.nullifier limb) +
  bindingSlice table fixed round 475 limb.val (pub.commitments 0 limb) +
  bindingSlice table fixed round 523 limb.val (pub.commitments 1 limb)

def digestValue (pub : Public) (table : BaseTable) (point : Fin 10 → K)
    (limb : Fin 8) : K :=
  digestHeadValue pub table point limb +
  ((∑ level : Fin 20, appendTermValue pub table point limb level) +
    bindingValue table point 859 limb.val (pub.nextRoot limb) +
      carryValue pub table point limb)

noncomputable def digestSlice (pub : Public) (table : BaseTable)
    (fixed : Fin 10 → K) (round : Fin 10) (limb : Fin 8) : K[X] :=
  digestHeadSlice pub table fixed round limb +
  (∑ level : Fin 20, appendTermSlice pub table fixed round limb level) +
  (bindingSlice table fixed round 859 limb.val (pub.nextRoot limb) +
    carrySlice pub table fixed round limb)

def scalarValue (pub : Public) (table : BaseTable) (point : Fin 10 → K)
    (which : Fin 2) : K :=
  if which.val = 0 then bindingValue table point 44 1 pub.asset
  else bindingValue table point 508 1 pub.asset + bindingValue table point 460 1 pub.asset

noncomputable def scalarSlice (pub : Public) (table : BaseTable)
    (fixed : Fin 10 → K) (round : Fin 10) (which : Fin 2) : K[X] :=
  if which.val = 0 then bindingSlice table fixed round 44 1 pub.asset
  else bindingSlice table fixed round 508 1 pub.asset +
    bindingSlice table fixed round 460 1 pub.asset

theorem degree_add_two {a b : K[X]} (ha : a.natDegree ≤ 2)
    (hb : b.natDegree ≤ 2) : (a + b).natDegree ≤ 2 :=
  (natDegree_add_le _ _).trans (max_le ha hb)

theorem appendTermSlice_degree (pub : Public) (table : BaseTable)
    (fixed : Fin 10 → K) (round : Fin 10) (limb : Fin 8) (level : Fin 20) :
    (appendTermSlice pub table fixed round limb level).natDegree ≤ 2 := by
  unfold appendTermSlice
  split <;> exact bindingSlice_degree _ _ _ _ _ _

theorem carrySlice_degree (pub : Public) (table : BaseTable)
    (fixed : Fin 10 → K) (round : Fin 10) (limb : Fin 8) :
    (carrySlice pub table fixed round limb).natDegree ≤ 2 := by
  unfold carrySlice
  split
  · exact bindingSlice_degree _ _ _ _ _ _
  · simp

theorem digestSlice_degree (pub : Public) (table : BaseTable)
    (fixed : Fin 10 → K) (round : Fin 10) (limb : Fin 8) :
    (digestSlice pub table fixed round limb).natDegree ≤ 2 := by
  unfold digestSlice
  apply degree_add_two
  · apply degree_add_two
    · unfold digestHeadSlice
      apply degree_add_two
      · apply degree_add_two
        · apply degree_add_two <;> exact bindingSlice_degree _ _ _ _ _ _
        · exact bindingSlice_degree _ _ _ _ _ _
      · exact bindingSlice_degree _ _ _ _ _ _
    · apply Polynomial.natDegree_sum_le_of_forall_le
      intro level _
      exact appendTermSlice_degree pub table fixed round limb level
  · exact degree_add_two (bindingSlice_degree _ _ _ _ _ _)
      (carrySlice_degree pub table fixed round limb)

theorem scalarSlice_degree (pub : Public) (table : BaseTable)
    (fixed : Fin 10 → K) (round : Fin 10) (which : Fin 2) :
    (scalarSlice pub table fixed round which).natDegree ≤ 2 := by
  unfold scalarSlice
  split
  · exact bindingSlice_degree table fixed round 44 1 pub.asset
  · exact degree_add_two
      (bindingSlice_degree table fixed round 508 1 pub.asset)
      (bindingSlice_degree table fixed round 460 1 pub.asset)

theorem appendTermSlice_eval_at (pub : Public) (table : BaseTable)
    (fixed : Fin 10 → K) (round : Fin 10) (limb : Fin 8) (level : Fin 20)
    (x : K) :
    (appendTermSlice pub table fixed round limb level).eval x =
      appendTermValue pub table (replaceCoordinate fixed round x) limb level := by
  unfold appendTermSlice appendTermValue
  split <;> exact bindingSlice_eval_at _ _ _ _ _ _ _

theorem carrySlice_eval_at (pub : Public) (table : BaseTable)
    (fixed : Fin 10 → K) (round : Fin 10) (limb : Fin 8) (x : K) :
    (carrySlice pub table fixed round limb).eval x =
      carryValue pub table (replaceCoordinate fixed round x) limb := by
  unfold carrySlice carryValue
  split
  · exact bindingSlice_eval_at _ _ _ _ _ _ _
  · simp

theorem scalarSlice_eval_at (pub : Public) (table : BaseTable)
    (fixed : Fin 10 → K) (round : Fin 10) (which : Fin 2) (x : K) :
    (scalarSlice pub table fixed round which).eval x =
      scalarValue pub table (replaceCoordinate fixed round x) which := by
  unfold scalarSlice scalarValue
  split <;> simp only [eval_add, bindingSlice_eval_at]

inductive Output where | digest (limb : Fin 8) | scalar (which : Fin 2)
  deriving DecidableEq, Fintype

def outputCoordinate : Output → Coordinate
  | .digest limb => .digest limb
  | .scalar which => .scalar which

noncomputable def bindingSpec (table : BaseTable) (row column : Nat)
    (expected : F) : CoordinateSlices (K := K) where
  value := fun point => bindingValue table point row column expected
  slice := fun fixed round => bindingSlice table fixed round row column expected
  degree := by
    intro fixed round
    exact (bindingSlice_degree table fixed round row column expected).trans (by omega)
  eval_at := fun fixed round x =>
    bindingSlice_eval_at table fixed round row column expected x

noncomputable def appendTermSpec (pub : Public) (table : BaseTable)
    (limb : Fin 8) (level : Fin 20) : CoordinateSlices (K := K) :=
  if pub.appendIndex.testBit level.val then
    bindingSpec table (16 * (34 + level.val) + 12) limb.val (pub.frontier level limb)
  else bindingSpec table (16 * (34 + level.val)) (8 + limb.val)
    (emptyRoot level limb + if limb.val = 7 then NODE_TWEAK else 0)

noncomputable def carrySpec (pub : Public) (table : BaseTable) (limb : Fin 8) :
    CoordinateSlices (K := K) :=
  if within : carryIndex pub.appendIndex < 20 then
    bindingSpec table (16 * (33 + carryIndex pub.appendIndex) + 11) limb.val
      (pub.nextFrontier ⟨carryIndex pub.appendIndex, within⟩ limb)
  else BooleanSuffixSourceAlgebra.zero

noncomputable def digestSpec (pub : Public) (table : BaseTable) (limb : Fin 8) :
    CoordinateSlices (K := K) :=
  add
    (add
      (add
        (add (bindingSpec table 907 limb.val (pub.anchor limb))
          (bindingSpec table 427 limb.val (pub.nullifier limb)))
        (bindingSpec table 475 limb.val (pub.commitments 0 limb)))
      (bindingSpec table 523 limb.val (pub.commitments 1 limb)))
    (add
      (add (finsetSum (appendTermSpec pub table limb))
        (bindingSpec table 859 limb.val (pub.nextRoot limb)))
      (carrySpec pub table limb))

noncomputable def scalarSpec (pub : Public) (table : BaseTable) (which : Fin 2) :
    CoordinateSlices (K := K) :=
  if which.val = 0 then bindingSpec table 44 1 pub.asset
  else add (bindingSpec table 508 1 pub.asset) (bindingSpec table 460 1 pub.asset)

theorem appendTermSpec_value (pub : Public) (table : BaseTable) (limb : Fin 8)
    (level : Fin 20) (point : Fin 10 → K) :
    (appendTermSpec pub table limb level).value point =
      appendTermValue pub table point limb level := by
  unfold appendTermSpec appendTermValue bindingSpec
  split <;> rfl

theorem carrySpec_value (pub : Public) (table : BaseTable) (limb : Fin 8)
    (point : Fin 10 → K) :
    (carrySpec pub table limb).value point = carryValue pub table point limb := by
  unfold carrySpec carryValue bindingSpec BooleanSuffixSourceAlgebra.zero
  split <;> rfl

theorem digestSpec_value (pub : Public) (table : BaseTable) (limb : Fin 8)
    (point : Fin 10 → K) :
    (digestSpec pub table limb).value point = digestValue pub table point limb := by
  simp only [digestSpec, digestValue, digestHeadValue, add_value, finsetSum_value,
    bindingSpec, appendTermSpec_value, carrySpec_value]

theorem scalarSpec_value (pub : Public) (table : BaseTable) (which : Fin 2)
    (point : Fin 10 → K) :
    (scalarSpec pub table which).value point = scalarValue pub table point which := by
  unfold scalarSpec scalarValue bindingSpec
  split <;> rfl

noncomputable def publicOutputSpec (pub : Public) (table : BaseTable)
    (output : Output) : CoordinateSlices (K := K) := match output with
  | .digest limb => digestSpec pub table limb
  | .scalar which => scalarSpec pub table which

noncomputable def publicSource (pub : Public) (table : BaseTable) (output : Output) :
    SourcePolynomial (booleanTable (publicOutputSpec pub table output)) :=
  BooleanSuffixSourceConstructor.source (publicOutputSpec pub table output)

theorem appendTermValue_boolean (pub : Public) (table : BaseTable)
    (limb : Fin 8) (level : Fin 20) (row : Fin 1024) :
    appendTermValue pub table (booleanTracePoint row) limb level = liftBase
      (if pub.appendIndex.testBit level.val then
        gate (row.val = 16 * (34 + level.val) + 12)
          (table row.val limb.val - pub.frontier level limb)
      else gate (row.val = 16 * (34 + level.val))
        (table row.val (8 + limb.val) -
          (emptyRoot level limb + if limb.val = 7 then NODE_TWEAK else 0))) := by
  unfold appendTermValue
  split <;> rw [bindingValue_boolean]

theorem liftBase_sum {I : Type*} [Fintype I] [DecidableEq I] (f : I → F) :
    liftBase (∑ i, f i) = ∑ i, liftBase (f i) := by
  simpa using liftBase_finsetSum (Finset.univ : Finset I) f

theorem carryValue_boolean (pub : Public) (table : BaseTable) (limb : Fin 8)
    (row : Fin 1024) : carryValue pub table (booleanTracePoint row) limb = liftBase
      (if within : carryIndex pub.appendIndex < 20 then
        gate (row.val = 16 * (33 + carryIndex pub.appendIndex) + 11)
          (table row.val limb.val -
            pub.nextFrontier ⟨carryIndex pub.appendIndex, within⟩ limb)
      else 0) := by
  unfold carryValue
  split <;> simp only [bindingValue_boolean, liftBase_zero]

theorem digestValue_boolean (pub : Public) (table : BaseTable) (limb : Fin 8)
    (row : Fin 1024) :
    digestValue pub table (booleanTracePoint row) limb =
      liftBase (digestResidual pub table row.val limb) := by
  unfold digestValue digestHeadValue digestResidual appendDigestResidual
  rw [bindingValue_boolean, bindingValue_boolean, bindingValue_boolean,
    bindingValue_boolean, bindingValue_boolean, carryValue_boolean]
  simp_rw [appendTermValue_boolean]
  simp only [liftBase_add, liftBase_sum]

theorem scalarValue_boolean (pub : Public) (table : BaseTable) (which : Fin 2)
    (row : Fin 1024) :
    scalarValue pub table (booleanTracePoint row) which =
      liftBase (scalarResidual pub table row.val which) := by
  unfold scalarValue scalarResidual
  split
  · exact bindingValue_boolean table 44 1 pub.asset row
  · rw [bindingValue_boolean, bindingValue_boolean, ← liftBase_add]

theorem booleanTable_eq_literal_residual (pub : Public) (table : BaseTable)
    (output : Output) (row : Fin 1024) :
    booleanTable (publicOutputSpec pub table output) row =
      liftBase (residual pub table (outputCoordinate output) row.val) := by
  cases output with
  | digest limb =>
      change (digestSpec pub table limb).value (booleanTracePoint row) = _
      rw [digestSpec_value]
      exact digestValue_boolean pub table limb row
  | scalar which =>
      change (scalarSpec pub table which).value (booleanTracePoint row) = _
      rw [scalarSpec_value]
      exact scalarValue_boolean pub table which row

/-- Source-shaped array interface: every binding consumes the same-index `z`
opening.  The Rust packed/factored loop and mutable-array refinement remain
open; this interface itself has no acceptance premise. -/
def rustBinding (selector : K) (z : RustArray) (column : Fin 16)
    (expected : F) : K := selector * (z column - liftBase expected)

theorem rustBinding_eq_bindingValue (table : BaseTable) (point : Fin 10 → K)
    (target : Nat) (column : Fin 16) (expected : F) :
    rustBinding (rowValue target point) (openingArray table point 0) column expected =
      bindingValue table point target column.val expected := by
  unfold rustBinding bindingValue
  rw [show openingArray table point 0 column = openValue table point column.val by rfl]

theorem source_initial_is_literal_residual (pub : Public) (table : BaseTable)
    (output : Output) :
    ((publicSource pub table output).restriction 0 []).eval 0 +
        ((publicSource pub table output).restriction 0 []).eval 1 =
      ∑ row : Fin 1024, liftBase (residual pub table
        (outputCoordinate output) row.val) := by
  rw [(publicSource pub table output).initialBoundary]
  apply Finset.sum_congr rfl
  intro row _
  exact booleanTable_eq_literal_residual pub table output row

#print axioms publicOutputSpec
#print axioms publicSource
#print axioms booleanTable_eq_literal_residual
#print axioms rustBinding_eq_bindingValue
#print axioms source_initial_is_literal_residual
end AspisV8Completion.SelectedPublicOutputsSourcePolynomial
