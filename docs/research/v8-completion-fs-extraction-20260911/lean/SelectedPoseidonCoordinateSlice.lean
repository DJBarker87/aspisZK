import SelectedPoseidonGenericAlgebra

/-! Exact one-coordinate restriction of the selected projected Poseidon oracle.

All three trace views and all selectors are multilinear openings of tables
fixed at the C1 commitment cut.  The nonlinear two-round calculation is then
performed in `QM31Exact[X]` using the same ring-generic expression as the
off-domain value.  The evaluation theorem below is structural: it does not
infer an off-domain value from the Boolean residual table.

The Boolean-row identification and final degree bound are intentionally kept
as the next leaf, so this file cannot be mistaken for a completed callback or
literal Rust refinement. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option maxRecDepth 3000

namespace AspisV8Completion.SelectedPoseidonCoordinateSlice
open Polynomial
open AspisFormal.HashMerkleModel
open AspisV5ComponentCQM31TowerExact
open AspisV8.PositivePackBinding
open AspisV8.SelectedSemanticRows
open AspisV8.SelectedSemanticLaneAggregation
open AspisV8Completion.SelectedRangeLaneCoordinateSlice
open AspisV8Completion.SelectedInitialOutputsSourcePolynomial
open AspisV8Completion.SelectedPoseidonGenericAlgebra

abbrev K := QM31Exact
abbrev F := M31Exact

def viewTable (table : BaseTable) (view : Fin 3) (lane : Nat) : Fin 1024 → K :=
  AspisV8Completion.SelectedValueAuxiliarySourcePolynomial.traceTable table view lane

def baseToK : F →+* K where
  toFun := liftBase
  map_one' := liftBase_one
  map_mul' := liftBase_mul
  map_zero' := liftBase_zero
  map_add' := liftBase_add

noncomputable def baseToPolynomial : F →+* K[X] :=
  Polynomial.C.comp baseToK

def blockTable : Fin 1024 → K := indicatorTable (fun row => row / 16 < 57)
def localTable (index : Fin 16) : Fin 1024 → K :=
  indicatorTable (fun row => row % 16 = index.val)

def blockValue (point : Fin 10 → K) : K := mleValue blockTable point
def selectorValue (point : Fin 10 → K) : State K := fun index =>
  mleValue (localTable index) point
def traceValue (table : BaseTable) (view : Fin 3) (point : Fin 10 → K) : State K :=
  fun lane => tableMLEValue point (viewTable table view lane.val)

noncomputable def blockSlice (fixed : Fin 10 → K) (round : Fin 10) : K[X] :=
  mleSlice blockTable fixed round
noncomputable def selectorSlice (fixed : Fin 10 → K) (round : Fin 10) :
    State K[X] := fun index => mleSlice (localTable index) fixed round
noncomputable def traceSlice (table : BaseTable) (view : Fin 3)
    (fixed : Fin 10 → K) (round : Fin 10) : State K[X] := fun lane =>
  openingSlice (viewTable table view lane.val) fixed round

/-- One actual unpacked off-domain coordinate before tower packing. -/
def coordinateValue (rc : RC) (table : BaseTable) (point : Fin 10 → K)
    (lane : Fin 16) : K :=
  residualCoordinate baseToK rc (blockValue point) (selectorValue point)
    (traceValue table 0 point) (traceValue table 1 point)
    (traceValue table 2 point) lane

/-- The same expression evaluated coefficientwise in the polynomial ring. -/
noncomputable def coordinateSlice (rc : RC) (table : BaseTable)
    (fixed : Fin 10 → K) (round : Fin 10) (lane : Fin 16) : K[X] :=
  residualCoordinate baseToPolynomial rc (blockSlice fixed round)
    (selectorSlice fixed round) (traceSlice table 0 fixed round)
    (traceSlice table 1 fixed round) (traceSlice table 2 fixed round) lane

theorem evalRingHom_base_compatible (x : K) :
    (Polynomial.evalRingHom x).comp baseToPolynomial = baseToK := by
  apply DFunLike.ext _ _
  intro value
  change (C (liftBase value)).eval x = liftBase value
  simp

theorem blockSlice_eval_at (fixed : Fin 10 → K) (round : Fin 10) (x : K) :
    (blockSlice fixed round).eval x = blockValue (replaceCoordinate fixed round x) :=
  mleSlice_eval_at blockTable fixed round x

theorem selectorSlice_eval_at (fixed : Fin 10 → K) (round : Fin 10) (x : K) :
    mapState (Polynomial.evalRingHom x) (selectorSlice fixed round) =
      selectorValue (replaceCoordinate fixed round x) := by
  funext index
  exact mleSlice_eval_at (localTable index) fixed round x

theorem traceSlice_eval_at (table : BaseTable) (view : Fin 3)
    (fixed : Fin 10 → K) (round : Fin 10) (x : K) :
    mapState (Polynomial.evalRingHom x) (traceSlice table view fixed round) =
      traceValue table view (replaceCoordinate fixed round x) := by
  funext lane
  exact openingSlice_eval_at (viewTable table view lane.val) fixed round x

/-- Substitution commutes with the complete nonlinear projected residual. -/
theorem coordinateSlice_eval_at (rc : RC) (table : BaseTable)
    (fixed : Fin 10 → K) (round : Fin 10) (lane : Fin 16) (x : K) :
    (coordinateSlice rc table fixed round lane).eval x =
      coordinateValue rc table (replaceCoordinate fixed round x) lane := by
  have block : (Polynomial.evalRingHom x) (blockSlice fixed round) =
      blockValue (replaceCoordinate fixed round x) :=
    blockSlice_eval_at fixed round x
  have mapped := residualCoordinate_map (Polynomial.evalRingHom x)
    baseToPolynomial baseToK (evalRingHom_base_compatible x) rc
    (blockSlice fixed round) (selectorSlice fixed round)
    (traceSlice table 0 fixed round) (traceSlice table 1 fixed round)
    (traceSlice table 2 fixed round) lane
  rw [block, selectorSlice_eval_at,
    traceSlice_eval_at, traceSlice_eval_at, traceSlice_eval_at] at mapped
  simpa [coordinateSlice, coordinateValue] using mapped.symm

#print axioms evalRingHom_base_compatible
#print axioms selectorSlice_eval_at
#print axioms traceSlice_eval_at
#print axioms coordinateSlice_eval_at
end AspisV8Completion.SelectedPoseidonCoordinateSlice
