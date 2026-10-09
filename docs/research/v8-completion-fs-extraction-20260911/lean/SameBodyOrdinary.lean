import SameBodyRelation
set_option autoImplicit false
namespace AspisV8Completion.SameBodyOrdinary
universe u
variable {K : Type u}
open SameBodyRelation (Word)

/-- Explicit arithmetic implementation interface, NOT algebraic field laws.
tryInv is the source's fallible inverse operation; proving it implements field
inversion and checking the sampled circle geometry are separate obligations. -/
structure Arithmetic (K : Type u) where
  zero : K
  one : K
  add : K → K → K
  sub : K → K → K
  mul : K → K → K
  square : K → K
  tryInv : K → Option K

structure Point (K : Type u) where
  x : K
  y : K

abbrev claimIndex (row : Fin 3) (lane : Fin 29) : Fin 697 :=
  ⟨271+29*row.val+lane.val, by omega⟩
abbrev oodIndex (row : Fin 2) (lane : Fin 29) : Fin 697 :=
  ⟨359+29*row.val+lane.val, by omega⟩
def claims (w : Word K) (r : Fin 3) (l : Fin 29) : K := w (claimIndex r l)
def ood (w : Word K) (r : Fin 2) (l : Fin 29) : K := w (oodIndex r l)

/-- The repaired row scales, never the disproved unshifted [1,k,k²]. -/
def scales (ops : Arithmetic K) (k : K) : Fin 3 → K :=
  fun i => if i.val=0 then k else if i.val=1 then ops.square k else ops.mul (ops.square k) k

/-- Literal forward powers/increment order from inactive_row_binding::prepare.
Equivalence to structured Horner/shared-gamma kernels remains arithmetic work. -/
def batch (ops : Arithmetic K) (gamma : K) (values : Fin 29 → K) : K :=
  ((List.finRange 29).foldl (fun state i =>
    (ops.add state.1 (ops.mul state.2 (values i)), ops.mul state.2 gamma))
    (ops.zero,ops.one)).1

def rowScalar (ops : Arithmetic K) (w : Word K) (gamma kappa : K) : K :=
  (List.finRange 3).foldl
    (fun c r => ops.add c (ops.mul (scales ops kappa r) (batch ops gamma (claims w r)))) (w 358)

structure Prepared (K : Type u) where
  useX : Bool
  scales : Fin 3 → K
  uncorrectedClaim : K
  oodBatches : Fin 2 → K
  intercept : K
  slope : K
  abc : Fin 3 → K
  denominatorInverse : K

/-- Construct ordinary scalar and chord/interpolant INPUTS from one word.
This stops before the selected public weight entries and affine correction;
it does not assume those entries, image validity or semantic acceptance. -/
def prepare [DecidableEq K] (ops : Arithmetic K) (w : Word K) (gamma kappa : K)
    (p0 p1 : Point K) : Option (Prepared K) :=
  let useX := decide (p0.x ≠ p1.x)
  let h0 := if useX then p0.x else p0.y
  let h1 := if useX then p1.x else p1.y
  match ops.tryInv (ops.sub h0 h1) with
  | none => none
  | some inv =>
    let y0 := batch ops gamma (ood w 0)
    let y1 := batch ops gamma (ood w 1)
    let slope := ops.mul (ops.sub y0 y1) inv
    some ⟨useX,scales ops kappa,rowScalar ops w gamma kappa,
      (fun r => if r.val=0 then y0 else y1),ops.sub y0 (ops.mul slope h0),slope,
      (fun r => if r.val=0 then ops.sub (ops.mul p0.x p1.y) (ops.mul p0.y p1.x)
        else if r.val=1 then ops.sub p0.y p1.y else ops.sub p1.x p0.x),inv⟩

theorem repaired_scales (ops : Arithmetic K) (k : K) :
    scales ops k 0 = k ∧ scales ops k 1 = ops.square k ∧
    scales ops k 2 = ops.mul (ops.square k) k := by
  simp [scales, show (2 : Fin 3).val = 2 from rfl]

theorem prepared_from_same_word [DecidableEq K] (ops : Arithmetic K) (w : Word K)
    (gamma kappa : K) (p0 p1 : Point K) (out : Prepared K)
    (success : prepare ops w gamma kappa p0 p1 = some out) :
    out.scales = scales ops kappa ∧
    out.uncorrectedClaim = rowScalar ops w gamma kappa ∧
    out.oodBatches 0 = batch ops gamma (ood w 0) ∧
    out.oodBatches 1 = batch ops gamma (ood w 1) ∧
    out.slope = ops.mul (ops.sub (batch ops gamma (ood w 0)) (batch ops gamma (ood w 1)))
      out.denominatorInverse ∧
    out.intercept = ops.sub (batch ops gamma (ood w 0))
      (ops.mul out.slope (if out.useX then p0.x else p0.y)) := by
  dsimp only [prepare] at success
  split at success
  · contradiction
  · cases success
    simp

/-- Source domain failure is retained, not a successful fallback value. -/
theorem inverse_failure [DecidableEq K] (ops : Arithmetic K) (w : Word K)
    (gamma kappa : K) (p0 p1 : Point K)
    (failure : ops.tryInv (ops.sub (if p0.x ≠ p1.x then p0.x else p0.y)
      (if p0.x ≠ p1.x then p1.x else p1.y)) = none) :
    prepare ops w gamma kappa p0 p1 = none := by
  by_cases h : p0.x = p1.x
  · simp [h] at failure
    simp [prepare, h, failure]
  · simp [h] at failure
    simp [prepare, h, failure]

theorem prepared_inverse_and_chord [DecidableEq K] (ops : Arithmetic K) (w : Word K)
    (gamma kappa : K) (p0 p1 : Point K) (out : Prepared K)
    (success : prepare ops w gamma kappa p0 p1 = some out) :
    out.useX = decide (p0.x ≠ p1.x) ∧
    ops.tryInv (ops.sub (if out.useX then p0.x else p0.y)
      (if out.useX then p1.x else p1.y)) = some out.denominatorInverse ∧
    out.abc 0 = ops.sub (ops.mul p0.x p1.y) (ops.mul p0.y p1.x) ∧
    out.abc 1 = ops.sub p0.y p1.y ∧ out.abc 2 = ops.sub p1.x p0.x := by
  dsimp only [prepare] at success
  split at success
  · contradiction
  next inv h =>
    cases success
    exact ⟨rfl,h,rfl,rfl,rfl⟩

theorem consumed_fields_fixed (w v : Word K)
    (same : ∀ i : Fin 697, 271 ≤ i.val → i.val < 417 → w i = v i) :
    claims w = claims v ∧ ood w = ood v ∧ w 358 = v 358 := by
  constructor
  · funext r l; exact same (claimIndex r l) (by simp [claimIndex]; omega) (by simp [claimIndex]; omega)
  constructor
  · funext r l; exact same (oodIndex r l) (by simp [oodIndex]; omega) (by simp [oodIndex]; omega)
  · exact same 358 (by decide) (by decide)

#print axioms repaired_scales
#print axioms prepared_from_same_word
#print axioms inverse_failure
#print axioms consumed_fields_fixed
#print axioms prepared_inverse_and_chord
end AspisV8Completion.SameBodyOrdinary
