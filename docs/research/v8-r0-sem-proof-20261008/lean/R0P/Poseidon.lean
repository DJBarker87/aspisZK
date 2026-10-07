import R0P.PoseidonConstants
import R0P.CoreExt
import R0P.Path

/-! G3 canonical scalar port, inspection pin e4d68a70d3f6beb215c9f6dd418f4a2a3740c809.
P = crates/aspis-statement/src/poseidon2.rs;
S = crates/aspis-statement/src/state_only_poseidon.rs;
T = crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs;
F = crates/aspis-core/src/field.rs.

The field functions transcribe P:137–170,200–218,339–352. The lead's
CoreExt and G3″ decisions authorize the unpacked canonical relation and its
base-typed packing equivalence. Refinement of the optimized raw-limb code
S:130–357,401–617 to this model remains a separate obligation.

The original unrestricted packing-kernel witness and the accepted G3′
endpoint counterexample are retained. The corrected G3″ iff characterizes
all committed transition rows; its endpoint theorem is forward only.
The block layout is the pair-forest caller's 57 blocks, not the generic
state-only module's 49-block default. No permutation or table is evaluated. -/
set_option autoImplicit false
namespace R0P
variable {K : Type} [Field K]

/-- P:137–140, pow5: retain both explicit square products. -/
def poseidonPow5 (value : K) : K :=
  let square := value * value
  square * square * value

/-- P:143–154, apply_mat4: exact temporary order and final output order. -/
def poseidonMat4 (values : Fin 4 → K) : Fin 4 → K :=
  let t01 := values 0 + values 1
  let t23 := values 2 + values 3
  let t0123 := t01 + t23
  let t01123 := t0123 + values 1
  let t01233 := t0123 + values 3
  let out3 := t01233 + (values 0 + values 0)
  let out1 := t01123 + (values 2 + values 2)
  let out0 := t01123 + t01
  let out2 := t01233 + t23
  ![out0, out1, out2, out3]

/-- P:157–170, external_linear: local groups first, then the four ordered
column sums, finally each state word plus its column sum. -/
def poseidonExternalLinear (state : Fin 16 → K) : Fin 16 → K :=
  let localState : Fin 4 → Fin 4 → K := fun group =>
    poseidonMat4 (fun lane => state ⟨4 * group.val + lane.val, by omega⟩)
  let sums : Fin 4 → K := fun column =>
    (((0 + localState 0 column) + localState 1 column) + localState 2 column) + localState 3 column
  fun index =>
    let group : Fin 4 := ⟨index.val / 4, by omega⟩
    let column : Fin 4 := ⟨index.val % 4, Nat.mod_lt _ (by omega)⟩
    localState group column + sums column

/-- P:208–218, internal_linear: retain the ordered nonzero-lane sum,
subtraction at lane zero and the literal shift-derived diagonal. -/
def poseidonInternalLinear (state : Fin 16 → K) : Fin 16 → K :=
  let partSum := (List.ofFn (fun i : Fin 15 => state i.succ)).foldl (· + ·) 0
  let fullSum := partSum + state 0
  fun index => if h : index.val = 0 then partSum - state 0
    else fullSum + state index * ((1 <<< poseidonInternalShifts
      ⟨index.val - 1, by omega⟩ : Nat) : K)

/-- P:200–205, full_round. -/
def poseidonFullRound (state constants : Fin 16 → K) : Fin 16 → K :=
  poseidonExternalLinear (fun lane => poseidonPow5 (state lane + constants lane))

/-- P:345–347, one internal round of the canonical permutation. -/
def poseidonInternalRound (state : Fin 16 → K) (constant : K) : Fin 16 → K :=
  poseidonInternalLinear (fun lane =>
    if lane = 0 then poseidonPow5 (state 0 + constant) else state lane)

/-- P:339–352, the explicit width-16 permutation evaluation, in source order.
No bijectivity over arbitrary K is asserted. The source pins M31. -/
def poseidonPermutation (state : Fin 16 → K) : Fin 16 → K :=
  let state := poseidonExternalLinear state
  let state := (List.ofFn (fun round : Fin 4 => poseidonExternalInitial (K := K) round)).foldl
    poseidonFullRound state
  let state := (List.ofFn (fun round : Fin 14 => poseidonInternalConstants (K := K) round)).foldl
    poseidonInternalRound state
  (List.ofFn (fun round : Fin 4 => poseidonExternalFinal (K := K) round)).foldl
    poseidonFullRound state

/-- P:62–68, round classes. Nat indices preserve the source enum's indices. -/
inductive PoseidonRoundKind
  | externalInitial (index : Nat)
  | internal (index : Nat)
  | externalFinal (index : Nat)
  deriving DecidableEq

/-- P:294–308, the descriptor's round-class branches, before reading constants. -/
def poseidonRoundKind (round : Nat) : Option PoseidonRoundKind :=
  if round < 4 then some (.externalInitial round)
  else if round < 4 + 14 then some (.internal (round - 4))
  else if round < 22 then some (.externalFinal (round - 4 - 14))
  else none

/-- P:239–253, the two round numbers assigned to a local transition row. -/
def poseidonRoundPair (localRow : Fin 11) : Nat × Nat :=
  (2 * localRow.val, 2 * localRow.val + 1)

/-- S:3–6,24–27 and T:211–216: pair-forest uses blocks 0 through 56,
with sixteen rows per block. The generic S:28 count 49 is not used here. -/
def poseidonBlockRow (block : Fin 57) (localRow : Fin 16) : Fin 1024 :=
  ⟨16 * block.val + localRow.val, by omega⟩

/-- F:946–950, the documented algebraic packing formula with EXPLICIT
parameters i,u. This is an obstruction witness, not the missing literal
QM31 implementation and not a Family or an assumed basis. -/
def poseidonPackingFormula (i u : K) (values : Fin 4 → K) : K :=
  values 0 + i * values 1 + u * values 2 + i * u * values 3

/-- No table evaluation: the canonical sbox's explicit products equal x^5. -/
theorem poseidon_pow5_eq (value : K) : poseidonPow5 value = value ^ 5 := by
  dsimp only [poseidonPow5]
  ring

/-- Symbolic row layout: local rows 0..10 each read the following row;
local row 11 is final output and row 12 carries the leading absorption. -/
theorem poseidon_block_layout (block : Fin 57) (localRow : Fin 11) :
    (poseidonBlockRow block (localRow.castLE (by omega))).val =
      16 * block.val + localRow.val ∧
    succRow (poseidonBlockRow block (localRow.castLE (by omega))) =
      poseidonBlockRow block ⟨localRow.val + 1, by omega⟩ ∧
    (poseidonBlockRow block 11).val = 16 * block.val + 11 ∧
    (poseidonBlockRow block 12).val = 16 * block.val + 12 := by
  refine ⟨rfl, ?_, rfl, rfl⟩
  apply Fin.ext
  simp only [succRow, poseidonBlockRow, Fin.val_mk, Fin.val_castLE]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- The field constant arrays remain opaque: this identifies the 4+14+4
round schedule at the eleven transition rows without evaluating a table. -/
theorem poseidon_round_pair_layout (localRow : Fin 11) :
    poseidonRoundPair localRow = (2 * localRow.val, 2 * localRow.val + 1) ∧
    (localRow.val = 0 →
      poseidonRoundKind (2 * localRow.val) = some (.externalInitial 0) ∧
      poseidonRoundKind (2 * localRow.val + 1) = some (.externalInitial 1)) ∧
    (localRow.val = 1 →
      poseidonRoundKind (2 * localRow.val) = some (.externalInitial 2) ∧
      poseidonRoundKind (2 * localRow.val + 1) = some (.externalInitial 3)) ∧
    (2 ≤ localRow.val → localRow.val ≤ 8 →
      poseidonRoundKind (2 * localRow.val) = some (.internal (2 * (localRow.val - 2))) ∧
      poseidonRoundKind (2 * localRow.val + 1) = some (.internal (2 * (localRow.val - 2) + 1))) ∧
    (localRow.val = 9 →
      poseidonRoundKind (2 * localRow.val) = some (.externalFinal 0) ∧
      poseidonRoundKind (2 * localRow.val + 1) = some (.externalFinal 1)) ∧
    (localRow.val = 10 →
      poseidonRoundKind (2 * localRow.val) = some (.externalFinal 2) ∧
      poseidonRoundKind (2 * localRow.val + 1) = some (.externalFinal 3)) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    simp only [h, poseidonRoundKind]
    norm_num
  · intro h
    simp only [h, poseidonRoundKind]
    norm_num
  · intro hlo hhi
    have h0 : ¬ 2 * localRow.val < 4 := by omega
    have h1 : ¬ 2 * localRow.val + 1 < 4 := by omega
    have h2 : 2 * localRow.val < 4 + 14 := by omega
    have h3 : 2 * localRow.val + 1 < 4 + 14 := by omega
    simp only [poseidonRoundKind, h0, h1, h2, h3, if_false, if_true, Option.some.injEq,
      PoseidonRoundKind.internal.injEq]
    omega
  · intro h
    simp only [h, poseidonRoundKind]
    norm_num
  · intro h
    simp only [h, poseidonRoundKind]
    norm_num

/-- A nonzero error in four unrestricted extension-field coordinates can
have zero packed value. In particular this applies to the source's i,u. -/
theorem poseidon_packing_kernel (i u : K) :
    poseidonPackingFormula i u ![-i, 1, 0, 0] = 0 ∧
      (![-i, 1, 0, 0] : Fin 4 → K) ≠ 0 := by
  constructor
  · change (-i) + i * 1 + u * 0 + i * u * 0 = 0
    ring
  · intro h
    have hx := congrFun h 1
    change (1 : K) = 0 at hx
    exact one_ne_zero hx

/-- Adding the same kernel error to a packed output preserves its packed
value. At an unconstrained final row this defeats the requested component
successor equivalence unless a base-field typing restriction is supplied. -/
theorem poseidon_packing_perturbation (i u : K) (values : Fin 4 → K) :
    poseidonPackingFormula i u ![values 0 - i, values 1 + 1, values 2, values 3] =
      poseidonPackingFormula i u values := by
  change (values 0 - i) + i * (values 1 + 1) + u * values 2 + i * u * values 3 =
    values 0 + i * values 1 + u * values 2 + i * u * values 3
  ring

/-- S:389–398 / 401–412, canonical field-level leading pair: absorb exactly
the eight rate words, apply the leading external layer, then initial rounds
zero and one. CoreExt and LOG's lead decision authorize this canonical model;
refinement of S's optimized raw-limb implementation remains a separate
obligation. No table is evaluated here. -/
def poseidonLeadingPair (state absorption : Fin 16 → K) : Fin 16 → K :=
  let state := fun lane =>
    if lane.val < 8 then state lane + absorption lane else state lane
  let state := poseidonExternalLinear state
  poseidonFullRound (poseidonFullRound state (poseidonExternalInitial 0))
    (poseidonExternalInitial 1)

/-- S:390–393 at a block's local row zero: xor12 reads local row twelve,
and only lanes zero through seven are absorbed before P:339–352. -/
def poseidonAbsorbedInput (A : Trace K) (block : Fin 57) : Fin 16 → K :=
  fun lane => if lane.val < 8 then
    A (lane.castAdd 13) (poseidonBlockRow block 0) +
      A (lane.castAdd 13) (poseidonBlockRow block 12)
    else A (lane.castAdd 13) (poseidonBlockRow block 0)

attribute [local irreducible] poseidonLeadingPair poseidonPermutation

/-- Endpoint correctness does not imply the source's selected successor
equations for this committed trace. All 57 outputs equal P:339–352 on the
absorbed inputs, while block zero's first successor word differs from its
S:389–398 leading pair by one. The permutation and constants stay opaque;
this is independent of the previously recorded packing obstruction. -/
theorem poseidon_endpoints_do_not_imply_successor :
    ∃ A : Trace K,
      (∀ block : Fin 57, ∀ lane : Fin 16,
        A (lane.castAdd 13) (poseidonBlockRow block 11) =
          poseidonPermutation (poseidonAbsorbedInput A block) lane) ∧
      A 0 (poseidonBlockRow 0 1) ≠
        poseidonLeadingPair
          (fun lane => A (lane.castAdd 13) (poseidonBlockRow 0 0))
          (fun lane => A (lane.castAdd 13) (poseidonBlockRow 0 12)) 0 := by
  let A : Trace K := fun column row =>
    if hc : column.val < 16 then
      if row.val % 16 = 11 then
        poseidonPermutation (0 : Fin 16 → K) ⟨column.val, hc⟩
      else if row.val = 1 ∧ column.val = 0 then
        poseidonLeadingPair (0 : Fin 16 → K) 0 0 + 1
      else 0
    else 0
  have hinput (block : Fin 57) :
      (fun lane : Fin 16 => A (lane.castAdd 13) (poseidonBlockRow block 0)) = 0 := by
    funext lane
    have hrow : (16 * block.val + 0) % 16 ≠ 11 := by omega
    have hfirst : ¬ (16 * block.val + 0 = 1 ∧ lane.val = 0) := by omega
    change (if hc : lane.val < 16 then
      if (16 * block.val + 0) % 16 = 11 then
        poseidonPermutation (0 : Fin 16 → K) ⟨lane.val, hc⟩
      else if 16 * block.val + 0 = 1 ∧ lane.val = 0 then
        poseidonLeadingPair (0 : Fin 16 → K) 0 0 + 1
      else 0
      else 0) = 0
    simp only [dif_pos lane.isLt, if_neg hrow, if_neg hfirst]
  have habsorption (block : Fin 57) :
      (fun lane : Fin 16 => A (lane.castAdd 13) (poseidonBlockRow block 12)) = 0 := by
    funext lane
    have hrow : (16 * block.val + 12) % 16 ≠ 11 := by omega
    have hfirst : ¬ (16 * block.val + 12 = 1 ∧ lane.val = 0) := by omega
    change (if hc : lane.val < 16 then
      if (16 * block.val + 12) % 16 = 11 then
        poseidonPermutation (0 : Fin 16 → K) ⟨lane.val, hc⟩
      else if 16 * block.val + 12 = 1 ∧ lane.val = 0 then
        poseidonLeadingPair (0 : Fin 16 → K) 0 0 + 1
      else 0
      else 0) = 0
    simp only [dif_pos lane.isLt, if_neg hrow, if_neg hfirst]
  have habsorbed (block : Fin 57) : poseidonAbsorbedInput A block = 0 := by
    funext lane
    have hz := congrFun (hinput block) lane
    have ha := congrFun (habsorption block) lane
    change A (lane.castAdd 13) (poseidonBlockRow block 0) = 0 at hz
    change A (lane.castAdd 13) (poseidonBlockRow block 12) = 0 at ha
    simp only [poseidonAbsorbedInput, hz, ha, zero_add, ite_self, Pi.zero_apply]
  refine ⟨A, ?_, ?_⟩
  · intro block lane
    rw [habsorbed block]
    have hrow : (16 * block.val + 11) % 16 = 11 := by omega
    change (if hc : lane.val < 16 then
      if (16 * block.val + 11) % 16 = 11 then
        poseidonPermutation (0 : Fin 16 → K) ⟨lane.val, hc⟩
      else if 16 * block.val + 11 = 1 ∧ lane.val = 0 then
        poseidonLeadingPair (0 : Fin 16 → K) 0 0 + 1
      else 0
      else 0) = poseidonPermutation (0 : Fin 16 → K) lane
    simp only [dif_pos lane.isLt, if_pos hrow, Fin.eta]
  · rw [hinput 0, habsorption 0]
    change poseidonLeadingPair (0 : Fin 16 → K) 0 0 + 1 ≠
      poseidonLeadingPair (0 : Fin 16 → K) 0 0
    intro h
    have hzero : (1 : K) = 0 := add_left_cancel
      (h.trans (add_zero (poseidonLeadingPair (0 : Fin 16 → K) 0 0)).symm)
    exact one_ne_zero hzero

/-! ## Continuation G3″: canonical scalar transitions

The lead decision after G3′ authorizes this field-level canonical relation.
S:130–357,401–617 raw-limb refinement remains the recorded separate obligation.
The definitions retain the selected three-branch residual and source ordering;
only lemmas restrict its selectors to Boolean rows. -/
attribute [local irreducible] poseidonExternalInitial poseidonExternalFinal
  poseidonInternalConstants poseidonInternalShifts poseidonPow5 poseidonMat4
  poseidonExternalLinear poseidonInternalLinear poseidonFullRound poseidonInternalRound

/-- P:294–308,200–218,339–352: apply the descriptor's canonical round.
The bounded round number makes the descriptor's out-of-range case impossible. -/
def poseidonApplyRound (round : Fin 22) (state : Fin 16 → K) : Fin 16 → K :=
  if h : round.val < 4 then
    poseidonFullRound state (poseidonExternalInitial ⟨round.val, h⟩)
  else if h' : round.val < 4 + 14 then
    poseidonInternalRound state (poseidonInternalConstants ⟨round.val - 4, by omega⟩)
  else poseidonFullRound state (poseidonExternalFinal ⟨round.val - 4 - 14, by omega⟩)

/-- S:389–398 and P:239–253,294–308: the selected canonical two-round step.
Only local row zero absorbs xor12 and applies the leading external layer. -/
def poseidonTransition (localRow : Fin 11) (state absorption : Fin 16 → K) : Fin 16 → K :=
  if localRow.val = 0 then poseidonLeadingPair state absorption else
    let pair := poseidonRoundPair localRow
    poseidonApplyRound ⟨pair.2, by dsimp [poseidonRoundPair, pair]; omega⟩
      (poseidonApplyRound ⟨pair.1, by dsimp [poseidonRoundPair, pair]; omega⟩ state)

/-- S:416–431,485–521, canonical field form of the ordered three-column
constant interpolation, under the lead's recorded raw-limb refinement boundary. -/
def poseidonInterpolatedFullPair (state : Fin 16 → K) (low : Fin 16 → K) : Fin 16 → K :=
  let even := fun lane =>
    (low 1 * poseidonExternalInitial 2 lane + low 9 * poseidonExternalFinal 0 lane) +
      low 10 * poseidonExternalFinal 2 lane
  let odd := fun lane =>
    (low 1 * poseidonExternalInitial 3 lane + low 9 * poseidonExternalFinal 1 lane) +
      low 10 * poseidonExternalFinal 3 lane
  poseidonFullRound (poseidonFullRound state even) odd

/-- S:524–535: local rows 2 through 8, ordered even/odd constant dot products.
Field operations are the lead-authorized canonical model of the limb code. -/
def poseidonInterpolatedInternalPair (state : Fin 16 → K) (low : Fin 16 → K) : Fin 16 → K :=
  let even := (List.ofFn (fun i : Fin 7 =>
    low ⟨i.val + 2, by omega⟩ * poseidonInternalConstants ⟨2 * i.val, by omega⟩)).foldl (· + ·) 0
  let odd := (List.ofFn (fun i : Fin 7 =>
    low ⟨i.val + 2, by omega⟩ * poseidonInternalConstants ⟨2 * i.val + 1, by omega⟩)).foldl (· + ·) 0
  poseidonInternalRound (poseidonInternalRound state even) odd

/-- S:589–615: unpacked canonical three-branch successor residual. The
leading/full/internal weights, block factor and lane order are retained.
F:606–630's prepared dot is represented by its ordered field products. -/
def poseidonScalarResidual (o : Openings K) (block : K) (low : Fin 16 → K) (lane : Fin 16) : K :=
  let leadingLow := low 0
  let fullLow := ([1, 9, 10] : List (Fin 16)).foldl (fun sum row => sum + low row) 0
  let internalLow := (List.ofFn (fun i : Fin 7 => low ⟨i.val + 2, by omega⟩)).foldl (· + ·) 0
  let leading := poseidonLeadingPair o.z o.xor12
  let full := poseidonInterpolatedFullPair o.z low
  let internal := poseidonInterpolatedInternalPair o.z low
  block * (((0 + leadingLow * (o.succ lane - leading lane)) +
    fullLow * (o.succ lane - full lane)) + internalLow * (o.succ lane - internal lane))

/-- T:211–216,1253–1255 and S:589–615, unpacked canonical relation.
Sixteen residuals are emitted, including prescribed inactive zeros. -/
def poseidonScalarFamily : Family K where
  residuals := fun _ o sel => List.ofFn (poseidonScalarResidual o
    (g2SumHigh sel 0 57 (by omega)) (g2Low sel))

private theorem poseidon_scalar_low (o : Openings K) (row : Fin 11) (lane : Fin 16) :
    poseidonScalarResidual o 1 (fun i => if i.val = row.val then 1 else 0) lane =
      o.succ lane - poseidonTransition row o.z o.xor12 lane := by
  fin_cases row <;>
    norm_num [poseidonScalarResidual, poseidonInterpolatedFullPair,
      poseidonInterpolatedInternalPair, poseidonTransition, poseidonApplyRound,
      poseidonRoundPair, List.ofFn_succ, List.foldl_cons, List.foldl_nil,
      show (9 : Fin 16).val = 9 from rfl, show (10 : Fin 16).val = 10 from rfl]
  all_goals first | rfl | (left; simp only [
    show (9 : Fin 16) ≠ 0 from by decide, show (10 : Fin 16) ≠ 0 from by decide,
    if_false, zero_add])

private theorem poseidon_scalar_low_inactive (o : Openings K) (block : K)
    (row : Fin 16) (hr : 11 ≤ row.val) (lane : Fin 16) :
    poseidonScalarResidual o block (fun i => if i.val = row.val then 1 else 0) lane = 0 := by
  have h0 : (0 : Nat) ≠ row.val := by omega
  have h1 : (1 : Nat) ≠ row.val := by omega
  have h9 : (9 : Nat) ≠ row.val := by omega
  have h10 : (10 : Nat) ≠ row.val := by omega
  have hi : (List.ofFn (fun i : Fin 7 =>
      (if (i.val + 2) = row.val then (1 : K) else 0))).foldl (· + ·) 0 = 0 := by
    have he : (fun i : Fin 7 => if i.val + 2 = row.val then (1 : K) else 0) = fun _ => 0 := by
      funext i; rw [if_neg (by omega)]
    rw [he, g2_fold_add]
    simp only [zero_add, List.sum_ofFn, Finset.sum_const_zero]
  simp only [poseidonScalarResidual, Fin.val_zero, Fin.val_one,
    show (9 : Fin 16).val = 9 from rfl, show (10 : Fin 16).val = 10 from rfl,
    if_neg h0, if_neg h1, if_neg h9, if_neg h10, List.foldl_cons, List.foldl_nil,
    zero_add, zero_mul, add_zero]
  rw [hi, zero_mul, mul_zero]

private theorem poseidon_scalar_block_zero (o : Openings K) (low : Fin 16 → K) (lane : Fin 16) :
    poseidonScalarResidual o 0 low lane = 0 := by
  exact zero_mul _

/-- Trace state notation; every word remains at its literal column and row. -/
abbrev poseidonState (A : Trace K) (block : Fin 57) (row : Fin 16) : Fin 16 → K :=
  fun lane => A (lane.castAdd 13) (poseidonBlockRow block row)

private theorem poseidon_xor12 (block : Fin 57) :
    xor12Row (poseidonBlockRow block 0) = poseidonBlockRow block 12 := by
  apply Fin.ext
  change (16 * block.val + 0) ^^^ 12 = 16 * block.val + 12
  have hd : ((16 * block.val) ^^^ 12) / 16 = block.val := by
    change ((2^4 * block.val) ^^^ 12) / 2^4 = block.val
    rw [Nat.xor_div_two_pow]
    simp
  have hm : ((16 * block.val) ^^^ 12) % 16 = 12 := by
    change ((2^4 * block.val) ^^^ 12) % 2^4 = 12
    rw [Nat.xor_mod_two_pow]
    simp
  rw [Nat.add_zero]
  omega

private theorem poseidon_transition_openings (A : Trace K) (block : Fin 57) (row : Fin 11) :
    poseidonTransition row (rowOpenings A (poseidonBlockRow block (row.castLE (by omega)))).z
      (rowOpenings A (poseidonBlockRow block (row.castLE (by omega)))).xor12 =
      poseidonTransition row (poseidonState A block (row.castLE (by omega)))
        (poseidonState A block 12) := by
  by_cases hr : row.val = 0
  · have he : row = 0 := Fin.ext hr
    subst row
    change poseidonLeadingPair (poseidonState A block 0)
      (fun lane => A (lane.castAdd 13) (xor12Row (poseidonBlockRow block 0))) = _
    rw [poseidon_xor12]
    rfl
  · simp only [poseidonTransition, if_neg hr]
    rfl

private theorem poseidon_scalar_at (A : Trace K) (block : Fin 57) (row : Fin 11) (lane : Fin 16) :
    poseidonScalarResidual (rowOpenings A (poseidonBlockRow block (row.castLE (by omega))))
      (g2SumHigh (rowSel (poseidonBlockRow block (row.castLE (by omega)))) 0 57 (by omega))
      (g2Low (rowSel (poseidonBlockRow block (row.castLE (by omega))))) lane =
      poseidonState A block ⟨row.val + 1, by omega⟩ lane -
        poseidonTransition row (poseidonState A block (row.castLE (by omega)))
          (poseidonState A block 12) lane := by
  have hh : (poseidonBlockRow block (row.castLE (by omega))).val / 16 = block.val := by
    dsimp [poseidonBlockRow]; omega
  have hl : (poseidonBlockRow block (row.castLE (by omega))).val % 16 = row.val := by
    dsimp [poseidonBlockRow]; omega
  have hlow : g2Low (rowSel (K := K) (poseidonBlockRow block (row.castLE (by omega)))) =
      (fun i => if i.val = row.val then 1 else 0) := by
    funext i; rw [g2_low_row, hl]
  rw [g2_sum_high_row, hh, if_pos (by omega), hlow, poseidon_scalar_low,
    poseidon_transition_openings]
  change A (lane.castAdd 13) (succRow (poseidonBlockRow block (row.castLE (by omega)))) - _ = _
  rw [(poseidon_block_layout block row).2.1]

private theorem poseidon_scalar_inactive (A : Trace K) (b : Fin 1024)
    (hb : ¬ (b.val / 16 < 57 ∧ b.val % 16 < 11)) (lane : Fin 16) :
    poseidonScalarResidual (rowOpenings A b) (g2SumHigh (rowSel b) 0 57 (by omega))
      (g2Low (rowSel b)) lane = 0 := by
  rw [g2_sum_high_row]
  by_cases hh : b.val / 16 < 57
  · rw [if_pos (by omega)]
    have hl : 11 ≤ b.val % 16 := by omega
    have hlow : g2Low (rowSel (K := K) b) =
        (fun i => if i.val = (⟨b.val % 16, Nat.mod_lt _ (by omega)⟩ : Fin 16).val then 1 else 0) := by
      funext i; exact g2_low_row b i
    rw [hlow]
    exact poseidon_scalar_low_inactive _ _ _ hl _
  · rw [if_neg (by omega), poseidon_scalar_block_zero]

private theorem poseidon_holds_lanes (pub : Public K) (A : Trace K) :
    Holds poseidonScalarFamily pub A ↔ ∀ b : Fin 1024, ∀ lane : Fin 16,
      poseidonScalarResidual (rowOpenings A b) (g2SumHigh (rowSel b) 0 57 (by omega))
        (g2Low (rowSel b)) lane = 0 := by
  constructor
  · intro h b lane
    exact h b _ (List.mem_ofFn.mpr ⟨lane, rfl⟩)
  · intro h b r hr
    obtain ⟨lane, rfl⟩ := List.mem_ofFn.mp hr
    exact h b lane

/-- Complete transition catalogue, including all committed intermediate rows.
S:389–398,589–615; P:239–253,294–308,339–352; T:211–216.
Only Boolean-row selector restriction is claimed. -/
theorem poseidon_scalar_holds_iff (pub : Public K) (A : Trace K) :
    Holds poseidonScalarFamily pub A ↔
      ∀ block : Fin 57, ∀ row : Fin 11, ∀ lane : Fin 16,
        poseidonState A block ⟨row.val + 1, by omega⟩ lane =
          poseidonTransition row (poseidonState A block (row.castLE (by omega)))
            (poseidonState A block 12) lane := by
  rw [poseidon_holds_lanes]
  constructor
  · intro h block row lane
    have hh := h (poseidonBlockRow block (row.castLE (by omega))) lane
    rw [poseidon_scalar_at] at hh
    exact sub_eq_zero.mp hh
  · intro h b lane
    by_cases hb : b.val / 16 < 57 ∧ b.val % 16 < 11
    · let block : Fin 57 := ⟨b.val / 16, hb.1⟩
      let row : Fin 11 := ⟨b.val % 16, hb.2⟩
      have he : b = poseidonBlockRow block (row.castLE (by omega)) := by
        apply Fin.ext; dsimp [poseidonBlockRow, block, row]; omega
      rw [he, poseidon_scalar_at]
      exact sub_eq_zero.mpr (h block row lane)
    · exact poseidon_scalar_inactive A b hb lane

omit [Field K] in
private theorem poseidon_fold_indices {α σ : Type} {n : Nat}
    (f : Fin n → α) (step : σ → α → σ) (a : σ) :
    (List.ofFn f).foldl step a =
      (List.ofFn (fun i : Fin n => i)).foldl (fun acc i => step acc (f i)) a := by
  calc
    (List.ofFn f).foldl step a =
        ((List.ofFn (fun i : Fin n => i)).map f).foldl step a := by rw [List.map_ofFn]; rfl
    _ = _ := List.foldl_map

omit [Field K] in
private theorem poseidon_fold_pairs {α σ : Type} {n : Nat}
    (f : Fin (2 * n) → α) (step : σ → α → σ) (a : σ) :
    (List.ofFn f).foldl step a =
      (List.ofFn (fun i : Fin n => i)).foldl
        (fun acc i => step (step acc (f ⟨2 * i.val, by omega⟩))
          (f ⟨2 * i.val + 1, by omega⟩)) a := by
  rw [List.ofFn_mul' f, List.foldl_flatten, poseidon_fold_indices]
  apply congrArg (fun g : σ → Fin n → σ => (List.ofFn (fun i : Fin n => i)).foldl g a)
  funext acc i
  simp only [List.ofFn_succ, List.ofFn_zero, List.foldl_cons, List.foldl_nil,
    Fin.val_zero, Fin.val_succ, Nat.add_zero, Nat.zero_add]

omit [Field K] in
private theorem poseidon_compose_steps {σ : Type} {n : Nat}
    (states : Fin (n + 1) → σ) (steps : Fin n → σ → σ)
    (h : ∀ i : Fin n, states i.succ = steps i (states i.castSucc)) :
    (List.ofFn steps).foldl (fun state step => step state) (states 0) = states (Fin.last n) := by
  induction n with
  | zero => simp only [List.ofFn_zero, List.foldl_nil, Fin.last_zero]
  | succ n ih =>
    rw [List.ofFn_succ, List.foldl_cons]
    have hz := h 0
    change states (Fin.succ 0) = steps 0 (states 0) at hz
    rw [← hz]
    exact ih (fun i => states i.succ) (fun i => steps i.succ) (fun i => h i.succ)

private theorem poseidon_rounds_split (state : Fin 16 → K) :
    (List.ofFn (fun r : Fin 22 => r)).foldl (fun s r => poseidonApplyRound r s) state =
      (List.ofFn (fun r : Fin 4 => poseidonExternalFinal (K := K) r)).foldl poseidonFullRound
        ((List.ofFn (fun r : Fin 14 => poseidonInternalConstants (K := K) r)).foldl poseidonInternalRound
          ((List.ofFn (fun r : Fin 4 => poseidonExternalInitial (K := K) r)).foldl
            poseidonFullRound state)) := by
  rw [List.ofFn_add (n := 4) (m := 18), List.foldl_append,
    List.ofFn_add (n := 14) (m := 4), List.foldl_append]
  simp only [poseidon_fold_indices]
  have hfirst : (fun (s : Fin 16 → K) (r : Fin 4) =>
      poseidonApplyRound (r.castLE (by omega)) s) =
      (fun s r => poseidonFullRound s (poseidonExternalInitial r)) := by
    funext s r
    simp only [poseidonApplyRound, Fin.val_castLE, dif_pos r.isLt]
  have hmiddle : (fun (s : Fin 16 → K) (r : Fin 14) =>
      poseidonApplyRound ((r.castLE (by omega) : Fin 18).natAdd 4) s) =
      (fun s r => poseidonInternalRound s (poseidonInternalConstants r)) := by
    funext s r
    have h0 : ¬ 4 + r.val < 4 := by omega
    have h1 : 4 + r.val < 4 + 14 := by omega
    simp only [poseidonApplyRound, Fin.val_natAdd, Fin.val_castLE, dif_neg h0, dif_pos h1]
    congr 2
    apply Fin.ext
    simp
  have hlast : (fun (s : Fin 16 → K) (r : Fin 4) =>
      poseidonApplyRound ((r.natAdd 14).natAdd 4) s) =
      (fun s r => poseidonFullRound s (poseidonExternalFinal r)) := by
    funext s r
    have h0 : ¬ 4 + (14 + r.val) < 4 := by omega
    have h1 : ¬ 4 + (14 + r.val) < 4 + 14 := by omega
    simp only [poseidonApplyRound, Fin.val_natAdd, dif_neg h0, dif_neg h1]
    congr 2
    apply Fin.ext
    change 4 + (14 + r.val) - 4 - 14 = r.val
    omega
  rw [hfirst, hmiddle, hlast]

private theorem poseidon_permutation_pairs (state : Fin 16 → K) :
    poseidonPermutation state =
      (List.ofFn (fun r : Fin 11 => r)).foldl (fun s r =>
        poseidonApplyRound ⟨2*r.val+1, by omega⟩
          (poseidonApplyRound ⟨2*r.val, by omega⟩ s)) (poseidonExternalLinear state) := by
  unfold poseidonPermutation
  rw [← poseidon_rounds_split]
  exact poseidon_fold_pairs (n := 11) (fun r => r)
    (fun s r => poseidonApplyRound r s) (poseidonExternalLinear state)

private theorem poseidon_transition_composition (state absorption : Fin 16 → K) :
    (List.ofFn (fun r : Fin 11 => fun s => poseidonTransition r s absorption)).foldl
      (fun state step => step state) state =
      poseidonPermutation (fun lane => if lane.val < 8 then state lane + absorption lane else state lane) := by
  rw [poseidon_permutation_pairs]
  rw [List.ofFn_succ, List.foldl_cons]
  conv => rhs; rw [List.ofFn_succ, List.foldl_cons]
  have hleading : poseidonApplyRound ⟨1, by omega⟩
      (poseidonApplyRound ⟨0, by omega⟩ (poseidonExternalLinear
        (fun lane => if lane.val < 8 then state lane + absorption lane else state lane))) =
      poseidonLeadingPair state absorption := by
    unfold poseidonLeadingPair
    simp only [poseidonApplyRound, dif_pos (show (1 : Nat) < 4 by omega),
      dif_pos (show (0 : Nat) < 4 by omega)]
    rfl
  change (List.ofFn (fun r : Fin 10 => fun s => poseidonTransition r.succ s absorption)).foldl
      (fun state step => step state) (poseidonLeadingPair state absorption) = _
  simp only [Fin.val_zero, Nat.mul_zero, zero_add] at *
  rw [hleading]
  conv => lhs; rw [poseidon_fold_indices]
  conv => rhs; rw [poseidon_fold_indices]
  apply congrArg (fun step : (Fin 16 → K) → Fin 10 → (Fin 16 → K) =>
    (List.ofFn (fun i : Fin 10 => i)).foldl step (poseidonLeadingPair state absorption))
  funext s r
  simp only [poseidonTransition, Fin.val_succ, Nat.add_one_ne_zero, if_false, poseidonRoundPair]

/-- Forward endpoint corollary of the complete transition catalogue. The
11 equations compose symbolically into P:339–352; no permutation value or
constant table is evaluated, and the accepted G3′ counterexample is retained. -/
theorem poseidon_scalar_holds_output (pub : Public K) (A : Trace K)
    (h : Holds poseidonScalarFamily pub A) :
    ∀ block : Fin 57, poseidonState A block 11 =
      poseidonPermutation (poseidonAbsorbedInput A block) := by
  intro block
  have ht := (poseidon_scalar_holds_iff pub A).mp h block
  have hc := poseidon_compose_steps
    (fun r : Fin 12 => poseidonState A block (r.castLE (by omega)))
    (fun r : Fin 11 => fun s => poseidonTransition r s (poseidonState A block 12))
    (fun r => funext (ht r))
  rw [poseidon_transition_composition] at hc
  exact hc.symm

omit [Field K] in
private theorem poseidon_vec_cons {α : Type} {n : Nat} (P : α → Prop)
    (head : α) (tail : Fin n → α) (hh : P head) (ht : ∀ i, P (tail i)) :
    ∀ i, P (Matrix.vecCons head tail i) := by
  intro i; exact Fin.cases hh ht i

omit [Field K] in
private theorem poseidon_vec_nil {α : Type} (P : α → Prop) :
    ∀ i, P (Matrix.vecEmpty (α := α) i) := by
  intro i; exact Fin.elim0 i

/-- Structural subfield closure of the literal vectors: only vector
constructors are traversed. Each numeral is discharged by the generic
natCast_mem theorem, without evaluating any table index or field value. -/
private theorem poseidon_initial_mem (F : Subfield K) :
    ∀ r lane, poseidonExternalInitial (K := K) r lane ∈ F := by
  unfold poseidonExternalInitial
  repeat' first
    | apply poseidon_vec_cons (fun row : Fin 16 → K => ∀ lane, row lane ∈ F)
    | apply poseidon_vec_nil (fun row : Fin 16 → K => ∀ lane, row lane ∈ F)
    | apply poseidon_vec_cons
    | apply poseidon_vec_nil
    | exact natCast_mem F _

private theorem poseidon_final_mem (F : Subfield K) :
    ∀ r lane, poseidonExternalFinal (K := K) r lane ∈ F := by
  unfold poseidonExternalFinal
  repeat' first
    | apply poseidon_vec_cons (fun row : Fin 16 → K => ∀ lane, row lane ∈ F)
    | apply poseidon_vec_nil (fun row : Fin 16 → K => ∀ lane, row lane ∈ F)
    | apply poseidon_vec_cons
    | apply poseidon_vec_nil
    | exact natCast_mem F _

private theorem poseidon_internal_constants_mem (F : Subfield K) :
    ∀ r, poseidonInternalConstants (K := K) r ∈ F := by
  unfold poseidonInternalConstants
  repeat' first
    | apply poseidon_vec_cons
    | apply poseidon_vec_nil
    | exact natCast_mem F _

private theorem poseidon_pow5_mem (F : Subfield K) (x : K) (hx : x ∈ F) :
    poseidonPow5 x ∈ F := by
  unfold poseidonPow5
  exact F.mul_mem (F.mul_mem (F.mul_mem hx hx) (F.mul_mem hx hx)) hx

private theorem poseidon_mat4_mem (F : Subfield K) (v : Fin 4 → K) (hv : ∀ i, v i ∈ F) :
    ∀ i, poseidonMat4 v i ∈ F := by
  unfold poseidonMat4
  repeat' first
    | apply poseidon_vec_cons
    | apply poseidon_vec_nil
    | apply F.add_mem
    | exact hv _

private theorem poseidon_external_mem (F : Subfield K) (v : Fin 16 → K) (hv : ∀ i, v i ∈ F) :
    ∀ i, poseidonExternalLinear v i ∈ F := by
  intro i
  unfold poseidonExternalLinear
  repeat' first
    | apply F.add_mem
    | exact F.zero_mem
    | apply poseidon_mat4_mem F
    | intro j
    | exact hv _

private theorem poseidon_internal_mem (F : Subfield K) (v : Fin 16 → K) (hv : ∀ i, v i ∈ F) :
    ∀ i, poseidonInternalLinear v i ∈ F := by
  have hs : (List.ofFn (fun i : Fin 15 => v i.succ)).foldl (· + ·) 0 ∈ F := by
    rw [g2_fold_add, zero_add]
    apply F.list_sum_mem
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hv i.succ
  intro i
  unfold poseidonInternalLinear
  split_ifs
  · exact F.sub_mem hs (hv 0)
  · exact F.add_mem (F.add_mem hs (hv 0))
      (F.mul_mem (hv i) (natCast_mem F _))

private theorem poseidon_full_round_mem (F : Subfield K) (v c : Fin 16 → K)
    (hv : ∀ i, v i ∈ F) (hc : ∀ i, c i ∈ F) :
    ∀ i, poseidonFullRound v c i ∈ F := by
  unfold poseidonFullRound
  apply poseidon_external_mem F
  intro i
  exact poseidon_pow5_mem F _ (F.add_mem (hv i) (hc i))

private theorem poseidon_internal_round_mem (F : Subfield K) (v : Fin 16 → K) (c : K)
    (hv : ∀ i, v i ∈ F) (hc : c ∈ F) :
    ∀ i, poseidonInternalRound v c i ∈ F := by
  unfold poseidonInternalRound
  apply poseidon_internal_mem F
  intro i
  split_ifs
  · exact poseidon_pow5_mem F _ (F.add_mem (hv 0) hc)
  · exact hv i

private theorem poseidon_leading_mem (F : Subfield K) (v a : Fin 16 → K)
    (hv : ∀ i, v i ∈ F) (ha : ∀ i, a i ∈ F) :
    ∀ i, poseidonLeadingPair v a i ∈ F := by
  unfold poseidonLeadingPair
  apply poseidon_full_round_mem F
  · apply poseidon_full_round_mem F
    · apply poseidon_external_mem F
      intro i; split_ifs
      · exact F.add_mem (hv i) (ha i)
      · exact hv i
    · exact poseidon_initial_mem F 0
  · exact poseidon_initial_mem F 1

private theorem poseidon_apply_round_mem (F : Subfield K) (r : Fin 22) (v : Fin 16 → K)
    (hv : ∀ i, v i ∈ F) : ∀ i, poseidonApplyRound r v i ∈ F := by
  unfold poseidonApplyRound
  split_ifs
  · exact poseidon_full_round_mem F _ _ hv (poseidon_initial_mem F _)
  · exact poseidon_internal_round_mem F _ _ hv (poseidon_internal_constants_mem F _)
  · exact poseidon_full_round_mem F _ _ hv (poseidon_final_mem F _)

private theorem poseidon_transition_mem (F : Subfield K) (r : Fin 11) (v a : Fin 16 → K)
    (hv : ∀ i, v i ∈ F) (ha : ∀ i, a i ∈ F) :
    ∀ i, poseidonTransition r v a i ∈ F := by
  unfold poseidonTransition
  split_ifs
  · exact poseidon_leading_mem F v a hv ha
  · exact poseidon_apply_round_mem F _ _ (poseidon_apply_round_mem F _ v hv)

private theorem poseidon_state_mem (F : Subfield K) (A : Trace K) (hA : BaseTyped F A)
    (block : Fin 57) (row : Fin 16) : ∀ lane, poseidonState A block row lane ∈ F := by
  intro lane
  exact hA (lane.castAdd 13) (by simp only [Fin.val_castAdd]; omega) _

private theorem poseidon_scalar_residual_mem (F : Subfield K) (A : Trace K) (hA : BaseTyped F A)
    (b : Fin 1024) (lane : Fin 16) :
    poseidonScalarResidual (rowOpenings A b) (g2SumHigh (rowSel b) 0 57 (by omega))
      (g2Low (rowSel b)) lane ∈ F := by
  by_cases hb : b.val / 16 < 57 ∧ b.val % 16 < 11
  · let block : Fin 57 := ⟨b.val / 16, hb.1⟩
    let row : Fin 11 := ⟨b.val % 16, hb.2⟩
    have he : b = poseidonBlockRow block (row.castLE (by omega)) := by
      apply Fin.ext; dsimp [poseidonBlockRow, block, row]; omega
    rw [he, poseidon_scalar_at]
    exact F.sub_mem (poseidon_state_mem F A hA block _ lane)
      (poseidon_transition_mem F row _ _ (poseidon_state_mem F A hA block _)
        (poseidon_state_mem F A hA block 12) lane)
  · rw [poseidon_scalar_inactive A b hb lane]
    exact F.zero_mem

/-- T:1253–1255, S:600–615: four consecutive base-limb residuals packed in
source lane order. This is the authorized field-level packed model; the
S:130–357,401–617 optimized raw-limb refinement remains a separate obligation. -/
def poseidonPackedFamily {F : Subfield K} (B : PackBasis F) : Family K where
  residuals := fun _ o sel => List.ofFn (fun group : Fin 4 =>
    pack4 B (fun limb : Fin 4 => poseidonScalarResidual o
      (g2SumHigh sel 0 57 (by omega)) (g2Low sel) ⟨4*group.val+limb.val, by omega⟩))

/-- Independent packing is injective on these base-typed successor residuals.
No raw-limb refinement, endpoint-only iff, or additional extraction premise
is asserted. All inactive packed/scalar lanes remain present and zero. -/
theorem poseidon_packed_iff_scalar (F : Subfield K) (B : PackBasis F)
    (pub : Public K) (A : Trace K) (hA : BaseTyped F A) :
    Holds (poseidonPackedFamily B) pub A ↔ Holds poseidonScalarFamily pub A := by
  rw [poseidon_holds_lanes]
  constructor
  · intro h b lane
    let group : Fin 4 := ⟨lane.val / 4, by omega⟩
    let limb : Fin 4 := ⟨lane.val % 4, Nat.mod_lt _ (by omega)⟩
    have hp := h b _ (List.mem_ofFn.mpr ⟨group, rfl⟩)
    have hs := (pack4_eq_zero_iff B _ (fun j =>
      poseidon_scalar_residual_mem F A hA b ⟨4*group.val+j.val, by omega⟩)).mp hp limb
    have he : (⟨4*group.val+limb.val, by omega⟩ : Fin 16) = lane := by
      apply Fin.ext; dsimp [group, limb]; omega
    rw [he] at hs
    exact hs
  · intro h b r hr
    obtain ⟨group, rfl⟩ := List.mem_ofFn.mp hr
    exact (pack4_eq_zero_iff B _ (fun j =>
      poseidon_scalar_residual_mem F A hA b ⟨4*group.val+j.val, by omega⟩)).mpr
      (fun j => h b ⟨4*group.val+j.val, by omega⟩)

#print axioms poseidon_state_mem
#print axioms poseidon_scalar_residual_mem
#print axioms poseidon_packed_iff_scalar

#print axioms poseidon_vec_cons
#print axioms poseidon_vec_nil
#print axioms poseidon_initial_mem
#print axioms poseidon_final_mem
#print axioms poseidon_internal_constants_mem
#print axioms poseidon_pow5_mem
#print axioms poseidon_mat4_mem
#print axioms poseidon_external_mem
#print axioms poseidon_internal_mem
#print axioms poseidon_full_round_mem
#print axioms poseidon_internal_round_mem
#print axioms poseidon_leading_mem
#print axioms poseidon_apply_round_mem
#print axioms poseidon_transition_mem

#print axioms poseidon_fold_indices
#print axioms poseidon_fold_pairs
#print axioms poseidon_compose_steps
#print axioms poseidon_rounds_split
#print axioms poseidon_permutation_pairs
#print axioms poseidon_transition_composition
#print axioms poseidon_scalar_holds_output

#print axioms poseidon_xor12
#print axioms poseidon_transition_openings
#print axioms poseidon_scalar_at
#print axioms poseidon_scalar_inactive
#print axioms poseidon_holds_lanes
#print axioms poseidon_scalar_holds_iff

#print axioms poseidon_scalar_low
#print axioms poseidon_scalar_low_inactive
#print axioms poseidon_scalar_block_zero

#print axioms poseidon_pow5_eq
#print axioms poseidon_block_layout
#print axioms poseidon_round_pair_layout
#print axioms poseidon_packing_kernel
#print axioms poseidon_packing_perturbation
#print axioms poseidon_endpoints_do_not_imply_successor
end R0P
