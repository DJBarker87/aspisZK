import SelectedSemanticLaneAggregationV2
import SameC1CheckedTransferFacts

/-! DRAFT: concrete Boolean-row 4+24+1 lane construction. The 57-block
Poseidon layout narrowly reuses V7PoseidonRowsFromTrace's symbolic /16,%16
argument, not its obsolete49-block profile or generated proof closure.
Rows are constructed from the same C1 semantic table and specified H helper.
The projected Rust oracle/round-constant/selector source correspondence stays
open; no `AllRowsZero` result is inferred from verifier acceptance here.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000
namespace AspisV8.SelectedConcreteRowLanes
open AspisFormal.ArithmetizationCore AspisFormal.HashMerkleModel
open AspisV5ComponentCQM31TowerExact
open AspisPool.V7FixedWidth29TupleList AspisPool.V7PairForestCuArithmeticEquivalences
open AspisV8.PositivePackBinding AspisV8.SelectedNoteRecovery
open AspisV8.PositiveTerminalInsertion
open AspisV8.SelectedSemanticRows AspisV8.SelectedSemanticTransfer
open AspisV8.EarlyC1LateProjection AspisV8.EarlyC1CopyCollision
open AspisV8.SelectedEarlyC1Amounts AspisV8.SelectedSemanticLaneAggregation
noncomputable section
abbrev K := QM31Exact

def stateLane (group slot : Fin 4) : Fin 16 := ⟨4*group.val+slot.val, by omega⟩
def groupOf (lane : Fin 16) : Fin 4 := ⟨lane.val/4, by omega⟩
def slotOf (lane : Fin 16) : Fin 4 := ⟨lane.val%4, Nat.mod_lt _ (by decide)⟩

theorem stateLane_group_slot (lane : Fin 16) : stateLane (groupOf lane) (slotOf lane) = lane := by
  apply Fin.ext
  simp only [stateLane, groupOf, slotOf]
  omega

def pairResidual (rc : RoundConstants) (t : BaseTable) (block : Fin 57)
    (pair : Fin 11) (lane : Fin 16) : F :=
  pairState t block.val (pair.val+1) lane -
    gateStep rc (2*pair.val+1) (gateStep rc (2*pair.val) (pairState t block.val pair.val)) lane

def poseidonRow (block : Fin 57) (pair : Fin 11) : Fin 1024 :=
  ⟨16*block.val+pair.val, by omega⟩

def poseidonCoordinate (rc : RoundConstants) (t : BaseTable)
    (row : Fin 1024) (group slot : Fin 4) : F :=
  if block : row.val/16 < 57 then
    if pair : row.val%16 < 11 then
      pairResidual rc t ⟨row.val/16,block⟩ ⟨row.val%16,pair⟩ (stateLane group slot)
    else 0
  else 0

theorem poseidonCoordinate_active (rc : RoundConstants) (t : BaseTable)
    (block : Fin 57) (pair : Fin 11) (group slot : Fin 4) :
    poseidonCoordinate rc t (poseidonRow block pair) group slot =
      pairResidual rc t block pair (stateLane group slot) := by
  have divided : (poseidonRow block pair).val/16 = block.val := by
    simp only [poseidonRow]
    omega
  have remainder : (poseidonRow block pair).val%16 = pair.val := by
    simp only [poseidonRow]
    omega
  unfold poseidonCoordinate
  simp only [divided, remainder, dif_pos block.isLt, dif_pos pair.isLt]

def packedPoseidon (rc : RoundConstants) (t : BaseTable)
    (row : Fin 1024) (group : Fin 4) : K :=
  literalPack (fun slot => liftBase (poseidonCoordinate rc t row group slot))

/-- Only base coordinates are unpacked. No four arbitrary QM31 residuals
are asserted independent under a QM31 packer. -/
theorem base_pack_zero (v : Fin 4 → F)
    (zero : literalPack (fun i => liftBase (v i)) = 0) : ∀ i, v i = 0 := by
  rw [literalPack_base_coordinates] at zero
  intro i
  fin_cases i
  · exact congrArg (fun x : K => x.re.re) zero
  · exact congrArg (fun x : K => x.re.im) zero
  · exact congrArg (fun x : K => x.im.re) zero
  · exact congrArg (fun x : K => x.im.im) zero

theorem packedPoseidon_zero_checks (rc : RoundConstants) (t : BaseTable)
    (zero : ∀ row group, packedPoseidon rc t row group = 0) : PoseidonChecks rc t := by
  intro block pair lane
  have packed := zero (poseidonRow block pair) (groupOf lane)
  have unpacked := base_pack_zero
    (poseidonCoordinate rc t (poseidonRow block pair) (groupOf lane)) packed (slotOf lane)
  rw [poseidonCoordinate_active, stateLane_group_slot] at unpacked
  exact unpacked

/-- Actual order of the selected two reverse-Horner loops: Poseidon0..3,
packed semantics4..27, selected copy28. The positive profile's 95 semantic
coordinates occupy24 groups; slot95 is a structural zero, not a dropped
honest-zero constraint. -/
def lanes (rc : RoundConstants) (pub : Public) (candidate : C1InitialMessages)
    (lambda chi : K) (helper : Fin 1024 → K) (row : Fin 1024) : RowLanes K where
  poseidon := packedPoseidon rc (semanticTable candidate) row
  semantic := packedRows pub (semanticTable candidate) row
  copy := SelectedSemanticRows.copyResidual (memberTable candidate) pub.appendIndex lambda chi helper row

theorem allRowsZero_constructs_residuals (rc : RoundConstants) (pub : Public)
    (candidate : C1InitialMessages) (lambda chi : K) (helper : Fin 1024 → K)
    (zero : AllRowsZero (lanes rc pub candidate lambda chi helper)) :
    RowsVanish pub (semanticTable candidate) ∧ PoseidonChecks rc (semanticTable candidate) ∧
      (∀ row, SelectedSemanticRows.copyResidual (memberTable candidate)
        pub.appendIndex lambda chi helper row = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · apply (packedRows_zero_iff pub (semanticTable candidate)).mp
    intro row group
    exact (zero row).2.1 group
  · apply packedPoseidon_zero_checks
    intro row group
    exact (zero row).1 group
  · intro row
    exact (zero row).2.2

/-- One tuple supplies both the C1 projection and H (lane26). This can be
instantiated with recoveredComponents without an independent candidate/H. -/
def tupleLanes (rc : RoundConstants) (pub : Public)
    (tuple : Fin 29 → Fin 1024 → K) (lambda chi : K) : Fin 1024 → RowLanes K :=
  lanes rc pub (c1Projection tuple) lambda chi (tuple 26)

theorem tupleRowsZero_constructs_residuals (rc : RoundConstants) (pub : Public)
    (tuple : Fin 29 → Fin 1024 → K) (lambda chi : K)
    (zero : AllRowsZero (tupleLanes rc pub tuple lambda chi)) :
    RowsVanish pub (semanticTable (c1Projection tuple)) ∧
      PoseidonChecks rc (semanticTable (c1Projection tuple)) ∧
      (∀ row, SelectedSemanticRows.copyResidual (memberTable (c1Projection tuple))
        pub.appendIndex lambda chi (tuple 26) row = 0) :=
  allRowsZero_constructs_residuals rc pub (c1Projection tuple) lambda chi (tuple 26) zero

#print tupleRowsZero_constructs_residuals
#print axioms poseidonCoordinate_active
#print axioms packedPoseidon_zero_checks
#print axioms allRowsZero_constructs_residuals
#print axioms tupleRowsZero_constructs_residuals
end
end AspisV8.SelectedConcreteRowLanes
