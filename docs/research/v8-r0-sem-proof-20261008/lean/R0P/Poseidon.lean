import R0P.PoseidonConstants

/-! G3 partial result, inspection pin e4d68a70d3f6beb215c9f6dd418f4a2a3740c809.
P = crates/aspis-statement/src/poseidon2.rs;
S = crates/aspis-statement/src/state_only_poseidon.rs;
T = crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs;
F = crates/aspis-core/src/field.rs.

STOP: no poseidonFamily or poseidon_holds_iff is declared. S:585–617 calls
QM31 limb operations and the tower packing F:946–989. Core supplies neither
that representation nor base-field typing of Trace K. The packing-kernel
lemma below prevents claiming sixteen successor equations from four packed
ones on unrestricted extension-valued traces.

The field functions below transcribe the canonical field-operation path
P:137–170,200–218,339–352. They are NOT claimed to be a literal port or a
proved refinement of the projected raw-limb implementation S:585–617.
The separate layout facts transcribe the pair-forest caller's 57 blocks,
not the generic state-only module's 49-block default. -/
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

#print axioms poseidon_pow5_eq
#print axioms poseidon_block_layout
#print axioms poseidon_round_pair_layout
#print axioms poseidon_packing_kernel
#print axioms poseidon_packing_perturbation
end R0P
