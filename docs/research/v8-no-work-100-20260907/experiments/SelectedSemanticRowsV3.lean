import SelectedAmountEndpoint
import SelectedAppendAfterstate
import SelectedCopyLayoutRows

/-!
Boolean-row model of the selected TRANSFER terminal, including the opt-in
positive-transfer source position94. The unmodified crate has94 base
positions; the positive profile has95, packed into24 QM31 lanes with slot95
zero. The copy lane and four Poseidon lanes are separate, never packed as
independent base coordinates. Occupancy ADDS into positions0..11; it is not
a replacement for initial-state constraints.

This is a source-shaped mathematical oracle, not a Rust execution theorem,
acceptance definition, or checked-witness claim. All source semantic terms
(including append public bindings and absorption zeros) are retained. Mask,
inactive-H, helper totals, caller checks and Poseidon constraints are not
deleted or inferred from the semantic projection below.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.SelectedSemanticRows
open scoped BigOperators
open AspisFormal.ArithmetizationCore AspisFormal.HashMerkleModel
open AspisV5ComponentCQM31TowerExact
open AspisV8.SelectedPaymentRecovery AspisV8.SelectedAmountEndpoint
open AspisV8.PositivePackBinding AspisV8.PositiveTerminalInsertion
open AspisV8.SelectedWeightedCopyRows AspisV8.SelectedCopyLayoutRows
noncomputable section

abbrev BaseTable := Nat → Nat → F

/-- Literal generated words, not a supplied correct-empty-root hypothesis.
No Poseidon evaluation of this constant table is attempted in this leaf. -/
@[irreducible] def emptyRootWords : Fin 21 → Fin 8 → Nat := ![
  ![1438900896, 782233260, 1544844157, 891350894, 986827501, 300047813, 266092546, 1155026732],
  ![141619947, 1448060902, 524379093, 1944458907, 1832113773, 579270723, 752346270, 1038346536],
  ![1119858538, 128294437, 939091034, 659145897, 1933666768, 903679201, 1182639487, 1398246146],
  ![1057897051, 1132946363, 794377079, 1971564389, 1255722275, 926653737, 2031728153, 2024887573],
  ![1410054462, 673771449, 940847521, 274330358, 1719505495, 1690439941, 203201419, 1855504616],
  ![1442759752, 1540325866, 188964047, 101815282, 1883549730, 1774537487, 1306717763, 561084592],
  ![244193611, 984304317, 1467689208, 2063463197, 1766003332, 1300835127, 1578947755, 745931587],
  ![673192756, 38070812, 1453532835, 1340577407, 368420458, 1834405704, 270061815, 711700631],
  ![27092219, 1272373356, 998194489, 1458413288, 887470405, 1204987730, 864453460, 553704718],
  ![1972918328, 1234090299, 977162835, 1704494754, 1617603773, 1819200880, 906453206, 1653526885],
  ![418360492, 472096212, 871749117, 98906847, 2026788776, 1504737042, 407274798, 1800828893],
  ![986339640, 660349625, 1012157959, 454024326, 987656904, 622864739, 1150440730, 1280042062],
  ![2118470693, 1706590589, 2128512933, 167263577, 409542414, 1323179656, 1880070613, 2053396184],
  ![260546973, 1375125357, 1584234519, 1097072342, 1685367984, 1070989054, 2113798037, 958210542],
  ![1239966481, 992485427, 1397515674, 466658549, 2071909237, 712995354, 2047452742, 1680224983],
  ![1796237568, 1862343136, 1954463912, 1190686266, 364700025, 46960257, 671215600, 1214723477],
  ![1127845264, 662862400, 84021756, 995080286, 1419670571, 1966281459, 837284626, 2083375353],
  ![1321679286, 782621548, 1415820264, 74436574, 776350425, 323154748, 429051705, 1299980413],
  ![1519171444, 1235587172, 1671492368, 1449613582, 547369941, 1621086153, 266860322, 450526803],
  ![19381883, 1308966873, 251977766, 474343397, 2069732268, 1863820229, 152153379, 665567443],
  ![1201428963, 1296676114, 441891487, 1910121140, 602621674, 1294160489, 1878016864, 855887413]]

def emptyRoot (level : Fin 20) (limb : Fin 8) : F :=
  (emptyRootWords ⟨level.val, by omega⟩ limb : F)

/-- The transfer public digest inputs. Their caller/account authority and
validate_transition's integer/static checks are separate obligations. -/
structure Public where
  asset : F
  anchor : Digest
  nullifier : Digest
  commitments : Fin 2 → Digest
  appendIndex : Nat
  frontier : Fin 20 → Digest
  nextRoot : Digest
  nextFrontier : Fin 20 → Digest

def gate (active : Prop) [Decidable active] (value : F) : F :=
  if active then value else 0

def firstBlock (block : Nat) : Prop :=
  block = 0 ∨ block = 1 ∨ block = 25 ∨ block = 27 ∨ block = 30
instance : DecidablePred firstBlock := fun _ => by unfold firstBlock; infer_instance

def nodeBlock (block : Nat) : Prop :=
  (4 ≤ block ∧ block < 25) ∨ (33 ≤ block ∧ block < 57)
instance : DecidablePred nodeBlock := fun _ => by unfold nodeBlock; infer_instance

def chunkTwo (block : Nat) : Prop := block = 3 ∨ block = 29 ∨ block = 32
instance : DecidablePred chunkTwo := fun _ => by unfold chunkTwo; infer_instance

def chunkEight (block : Nat) : Prop :=
  block = 0 ∨ block = 1 ∨ block = 2 ∨ block = 25 ∨ block = 26 ∨
    block = 27 ∨ block = 28 ∨ block = 30 ∨ block = 31
instance : DecidablePred chunkEight := fun _ => by unfold chunkEight; infer_instance

def firstDomain (block : Nat) : F :=
  if block = 0 then DOM_OWNER else if block = 25 then DOM_NULLIFIER else DOM_NOTE
def firstLength (block : Nat) : F :=
  if block = 0 then 8 else if block = 25 then 16 else 18

/-- Boolean specialization of semantic_initial_and_absorption for transfer.
The two block families are disjoint; no old77 row selector is substituted. -/
def initialResidual (t : BaseTable) (row : Nat) (column : Fin 16) : F :=
  gate (row % 16 = 0 ∧ firstBlock (row / 16))
      (t row column.val - initState (firstDomain (row / 16)) (firstLength (row / 16)) column) +
    gate (row % 16 = 0 ∧ nodeBlock (row / 16) ∧ column.val < 8) (t row column.val)

def absorptionResidual (t : BaseTable) (row : Nat) (column : Fin 16) : F :=
  gate (row % 16 = 12 ∧
    ((2 ≤ column.val ∧ column.val < 8 ∧ chunkTwo (row / 16)) ∨
      (8 ≤ column.val ∧ (chunkTwo (row / 16) ∨ chunkEight (row / 16) ∨
        nodeBlock (row / 16))))) (t row column.val)

/-- Algebraically normalized form of high[57..63] times low[1,5,9,13]. -/
def pathMask (row : Nat) : Prop := 912 ≤ row ∧ row < 1008 ∧ row % 4 = 1
instance : DecidablePred pathMask := fun _ => by unfold pathMask; infer_instance

theorem pathMask_source (row : Nat) :
    pathMask row ↔ (57 ≤ row / 16 ∧ row / 16 < 63) ∧
      (row % 16 = 1 ∨ row % 16 = 5 ∨ row % 16 = 9 ∨ row % 16 = 13) := by
  unfold pathMask
  omega

def directionResidual (t : BaseTable) (row : Nat) : F :=
  gate (pathMask row) (t row 0 * (t row 0 - 1))
def leftResidual (t : BaseTable) (row : Nat) (limb : Fin 8) : F :=
  gate (pathMask row) ((1 - t row 0) * (t (row + 1) limb.val - t row (1 + limb.val)))
def rightResidual (t : BaseTable) (row : Nat) (limb : Fin 8) : F :=
  gate (pathMask row) (t row 0 * (t (row + 1) (8 + limb.val) - t row (1 + limb.val)))

def valueMask (row : Nat) : Prop := row = 1008 ∨ row = 1010 ∨ row = 1012
instance : DecidablePred valueMask := fun _ => by unfold valueMask; infer_instance

def bitAt (t : BaseTable) (row : Nat) (bit : Fin 30) : F :=
  t (if bit.val < 10 then row else if bit.val < 20 then row + 1 else Nat.xor row 12)
    (bit.val % 10)
def viewRow (row : Nat) (view : Fin 3) : Nat :=
  if view.val = 0 then row else if view.val = 1 then row + 1 else Nat.xor row 12

/-- The source's exact reverse-Horner ten-bit helper. -/
def tenAt (t : BaseTable) (row : Nat) : F :=
  sourceHorner (t row) 9 (t row 9)
def reconstructAt (t : BaseTable) (row : Nat) : F :=
  ∑ view : Fin 3, tenAt t (viewRow row view) * (2 : F) ^ (10 * view.val)

theorem reconstructAt_source (t : BaseTable) (row : Nat) :
    reconstructAt t row = tenAt t row +
      tenAt t (row + 1) * (2 : F)^10 +
      tenAt t (Nat.xor row 12) * (2 : F)^20 := by
  simp [reconstructAt, viewRow, Fin.sum_univ_succ, add_assoc]

/-- Twelve gates share the existing initial position numbers, at disjoint
rows1017/1018. Position11 is input spend versus transfer output occupied=1. -/
def occupancyResidual (t : BaseTable) (row column : Nat) : F :=
  if column = 0 then gate (row = 1017 ∨ row = 1018) (t row 0 * (t row 0 - 1))
  else if column = 1 then gate (row = 1017 ∨ row = 1018) (t row 9 * t row 1 - t row 0)
  else if column = 2 then gate (row = 1017 ∨ row = 1018) ((1 - t row 0) * t row 1)
  else if column < 11 then gate (row = 1017 ∨ row = 1018) ((1 - t row 0) * t row (column - 1))
  else if column = 11 then gate (row = 1017) (t row 10 * (1 - t row 0)) +
    gate (row = 1018) (t row 0 - 1)
  else 0

def appendDigestResidual (pub : Public) (t : BaseTable)
    (row : Nat) (limb : Fin 8) : F :=
  (∑ level : Fin 20,
    if pub.appendIndex.testBit level.val then
      gate (row = 16 * (34 + level.val) + 12) (t row limb.val - pub.frontier level limb)
    else
      gate (row = 16 * (34 + level.val))
        (t row (8 + limb.val) - (emptyRoot level limb + if limb.val = 7 then NODE_TWEAK else 0))) +
  gate (row = 859) (t row limb.val - pub.nextRoot limb) +
  if within : SelectedAppendAfterstate.carryIndex pub.appendIndex < 20 then
    gate (row = 16 * (33 + SelectedAppendAfterstate.carryIndex pub.appendIndex) + 11)
      (t row limb.val -
        pub.nextFrontier ⟨SelectedAppendAfterstate.carryIndex pub.appendIndex, within⟩ limb)
  else 0

/-- All selected public-digest terms, including append sibling/root/carry
terms, are added exactly as in public_digest_lanes. -/
def digestResidual (pub : Public) (t : BaseTable)
    (row : Nat) (limb : Fin 8) : F :=
  gate (row = 907) (t row limb.val - pub.anchor limb) +
  gate (row = 427) (t row limb.val - pub.nullifier limb) +
  gate (row = 475) (t row limb.val - pub.commitments 0 limb) +
  gate (row = 523) (t row limb.val - pub.commitments 1 limb) +
  appendDigestResidual pub t row limb

def scalarResidual (pub : Public) (t : BaseTable)
    (row : Nat) (which : Fin 2) : F :=
  if which.val = 0 then gate (row = 44) (t row 1 - pub.asset)
  else gate (row = 508) (t row 1 - pub.asset) +
    gate (row = 460) (t row 1 - pub.asset)

inductive Coordinate where
  | initial (column : Fin 16)
  | absorption (column : Fin 16)
  | direction
  | left (limb : Fin 8)
  | right (limb : Fin 8)
  | rangeBit (bit : Fin 30)
  | recomposition
  | auxiliaryNext
  | auxiliaryXor
  | conservation (which : Fin 2)
  | digest (limb : Fin 8)
  | scalar (which : Fin 2)
  | positive
  deriving DecidableEq, Fintype

def position : Coordinate → Nat
  | .initial column => column.val
  | .absorption column => 16 + column.val
  | .direction => 32
  | .left limb => 33 + limb.val
  | .right limb => 41 + limb.val
  | .rangeBit bit => 49 + bit.val
  | .recomposition => 79
  | .auxiliaryNext => 80
  | .auxiliaryXor => 81
  | .conservation which => 82 + which.val
  | .digest limb => 84 + limb.val
  | .scalar which => 92 + which.val
  | .positive => 94

/-- Symbolic constructor census; never enumerate the95 coordinate values. -/
private def coordinateEquiv : Coordinate ≃ (Fin 16 ⊕ Fin 16 ⊕ Unit ⊕ Fin 8 ⊕ Fin 8 ⊕ Fin 30 ⊕ Unit ⊕ Unit ⊕ Unit ⊕ Fin 2 ⊕ Fin 8 ⊕ Fin 2 ⊕ Unit) where
  toFun
    | .initial x => Sum.inl (x)
    | .absorption x => Sum.inr (Sum.inl (x))
    | .direction => Sum.inr (Sum.inr (Sum.inl (())))
    | .left x => Sum.inr (Sum.inr (Sum.inr (Sum.inl (x))))
    | .right x => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (x)))))
    | .rangeBit x => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (x))))))
    | .recomposition => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (())))))))
    | .auxiliaryNext => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (()))))))))
    | .auxiliaryXor => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (())))))))))
    | .conservation x => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (x))))))))))
    | .digest x => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (x)))))))))))
    | .scalar x => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (x))))))))))))
    | .positive => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (()))))))))))))
  invFun
    | Sum.inl (x) => .initial x
    | Sum.inr (Sum.inl (x)) => .absorption x
    | Sum.inr (Sum.inr (Sum.inl (_))) => .direction
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl (x)))) => .left x
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (x))))) => .right x
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (x)))))) => .rangeBit x
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (_))))))) => .recomposition
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (_)))))))) => .auxiliaryNext
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (_))))))))) => .auxiliaryXor
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (x)))))))))) => .conservation x
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (x))))))))))) => .digest x
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (x)))))))))))) => .scalar x
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (_)))))))))))) => .positive
  left_inv := by intro coordinate; cases coordinate <;> rfl
  right_inv := by
    intro value
    rcases value with x | x | ⟨⟩ | x | x | x | ⟨⟩ | ⟨⟩ | ⟨⟩ | x | x | x | ⟨⟩ <;> rfl

theorem coordinate_count : Fintype.card Coordinate = 95 := by
  simpa using Fintype.card_congr coordinateEquiv

theorem position_lt (coordinate : Coordinate) : position coordinate < 95 := by
  cases coordinate <;> simp only [position] <;> omega

theorem position_injective : Function.Injective position := by
  intro left right same
  cases left <;> cases right <;> simp_all [position, Fin.ext_iff] <;> omega

def residual (pub : Public) (t : BaseTable) : Coordinate → Nat → F
  | .initial column, row => initialResidual t row column + occupancyResidual t row column.val
  | .absorption column, row => absorptionResidual t row column
  | .direction, row => directionResidual t row
  | .left limb, row => leftResidual t row limb
  | .right limb, row => rightResidual t row limb
  | .rangeBit bit, row => gate (valueMask row) ((bitAt t row bit)^2 - bitAt t row bit)
  | .recomposition, row => gate (valueMask row) (t row 10 - reconstructAt t row)
  | .auxiliaryNext, row => gate (valueMask row) (t (row + 1) 10)
  | .auxiliaryXor, row => gate (valueMask row) (t (Nat.xor row 12) 10)
  | .conservation which, row =>
      if which.val = 0 then gate (row = 1014) (t row 0 - t row 1 - t row 2)
      else gate (row = 1014) (t (row + 1) 0 - t (row + 1) 1)
  | .digest limb, row => digestResidual pub t row limb
  | .scalar which, row => scalarResidual pub t row which
  | .positive, row => gate (row = 1014) (t row 1 * t (row + 1) 1 * t row 3 - 1)

def packedLane (coordinate : Coordinate) : Fin 24 :=
  ⟨position coordinate / 4, by have := position_lt coordinate; omega⟩
def packedSlot (coordinate : Coordinate) : Fin 4 :=
  ⟨position coordinate % 4, Nat.mod_lt _ (by decide)⟩
def packedLocation (coordinate : Coordinate) : Fin 24 × Fin 4 :=
  (packedLane coordinate, packedSlot coordinate)

theorem packed_recovers_position (coordinate : Coordinate) :
    4 * (packedLane coordinate).val + (packedSlot coordinate).val = position coordinate := by
  simp only [packedLane, packedSlot]
  omega

theorem packedLocation_injective : Function.Injective packedLocation := by
  intro left right same
  apply position_injective
  have values := congrArg (fun location : Fin 24 × Fin 4 => 4 * location.1.val + location.2.val) same
  simpa only [packedLocation, packed_recovers_position] using values

/-- Reuses the V7 atomic row-sum construction, now with the actual95
positions and24 groups. It does not use V7's hardcoded20-group record. -/
def rows (pub : Public) (t : BaseTable) (row : Fin 1024)
    (group : Fin 24) (slot : Fin 4) : F :=
  ∑ coordinate : Coordinate,
    if packedLocation coordinate = (group, slot) then residual pub t coordinate row.val else 0

theorem rows_at_coordinate (pub : Public) (t : BaseTable)
    (coordinate : Coordinate) (row : Fin 1024) :
    rows pub t row (packedLane coordinate) (packedSlot coordinate) =
      residual pub t coordinate row.val := by
  classical
  unfold rows
  rw [Finset.sum_eq_single coordinate]
  · simp [packedLocation]
  · intro other _ different
    have unequal : packedLocation other ≠ packedLocation coordinate := fun same =>
      different (packedLocation_injective same)
    have targetUnequal : packedLocation other ≠ (packedLane coordinate, packedSlot coordinate) :=
      unequal
    simp only [if_neg targetUnequal]
  · simp

def RowsVanish (pub : Public) (t : BaseTable) : Prop :=
  ∀ row group slot, rows pub t row group slot = 0

theorem coordinate_zero (pub : Public) (t : BaseTable)
    (vanish : RowsVanish pub t) (coordinate : Coordinate) (row : Fin 1024) :
    residual pub t coordinate row.val = 0 := by
  rw [← rows_at_coordinate]
  exact vanish row (packedLane coordinate) (packedSlot coordinate)

/-- Actual literal QM31 packer, with base-valued Boolean coordinates. -/
def packedRows (pub : Public) (t : BaseTable) (row : Fin 1024) (group : Fin 24) : QM31Exact :=
  literalPack (fun slot => liftBase (rows pub t row group slot))

/-- Abstract-vector separation prevents reduction of the concrete finite
row oracle when projecting a nested tower constructor. -/
theorem base_coordinates_zero (v : Fin 4 → M31Exact)
    (zero : (⟨⟨v 0,v 1⟩,⟨v 2,v 3⟩⟩ : QM31Exact) = 0) :
    ∀ slot, v slot = 0 := by
  intro slot
  fin_cases slot
  · exact congrArg (fun value : QM31Exact => value.re.re) zero
  · exact congrArg (fun value : QM31Exact => value.re.im) zero
  · exact congrArg (fun value : QM31Exact => value.im.re) zero
  · exact congrArg (fun value : QM31Exact => value.im.im) zero

theorem packedRows_zero_iff (pub : Public) (t : BaseTable) :
    (∀ row group, packedRows pub t row group = 0) ↔ RowsVanish pub t := by
  constructor
  · intro vanish row group slot
    have zero := vanish row group
    rw [packedRows, literalPack_base_coordinates] at zero
    exact base_coordinates_zero (rows pub t row group) zero slot
  · intro vanish row group
    rw [packedRows, literalPack_base_coordinates]
    simp only [vanish row group]
    rfl

/-- The95 base-position oracle does NOT pack this extension-valued lane.
It uses the already-proved actual136-link row constructor, independent
public weights, fixed active mask and all four denominator factors. -/
def copyResidual (table : SelectedCopyLayoutRows.Table QM31Exact)
    (appendIndex : Nat) (lambda chi : QM31Exact) (helper : Fin 1024 → QM31Exact)
    (row : Fin 1024) : QM31Exact :=
  selectedBooleanResidual (sourceRows table lambda .transfer appendIndex) helper chi row

#print axioms pathMask_source
#print axioms reconstructAt_source
#print axioms coordinate_count
#print axioms position_lt
#print axioms position_injective
#print axioms packed_recovers_position
#print axioms packedLocation_injective
#print axioms rows_at_coordinate
#print axioms coordinate_zero
#print axioms base_coordinates_zero
#print axioms packedRows_zero_iff
end
end AspisV8.SelectedSemanticRows

