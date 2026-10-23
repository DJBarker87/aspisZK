import AspisR1S9ActualWeightsNewBoxNewV3.Funs
import S9ConstructorV3QMMulCanonicalV1
import S9ConstructorV3DoubleCanonicalV1
import S9ConstructorV3QMAddSubCanonicalV1
import S9PairArrayUpdateCanonicalV1
import S9CandidateFoldMapPrimitivesV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1S9ConstructorV3Loop1CellCanonicalV1

abbrev Q := AspisR1S9ActualWeightsNewBoxNewV3.field.QM31
abbrev ProbeQ := AspisR1S9ActualQM31WrappingMapV1.ProbeQM
abbrev CanQ := AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
abbrev Cell := Array Q (4#usize)
abbrev Row := Array Cell (5#usize)
abbrev Factors := Array Row (5#usize)
abbrev R := core.ops.range.Range Std.Usize

def toProbeQ (x : Q) : ProbeQ :=
  AspisR1S9ConstructorV3QMMulCanonicalV1.toProbe x

def mapCells (a : Cell) : Array ProbeQ (4#usize) :=
  AspisR1S9CandidateFoldMapPrimitivesV1.mapArray toProbeQ a

def mapRow (a : Row) : Array (Array ProbeQ (4#usize)) (5#usize) :=
  AspisR1S9CandidateFoldMapPrimitivesV1.mapArray mapCells a

def CellsCanonical (a : Array ProbeQ (4#usize)) : Prop :=
  ∀ (j : Std.Usize) (v : ProbeQ),
    Array.index_usize a j = .ok v → CanQ v

private theorem index_success_bound {A : Type} {N : Std.Usize}
    (a : Array A N) (i : Std.Usize) (x : A)
    (h : Array.index_usize a i = .ok x) : i.val < N.val := by
  unfold Array.index_usize at h
  cases hopt : a[i]? with
  | none => simp [hopt] at h
  | some y =>
      have hsome : a.val[i.val]? = some y := by simpa using hopt
      have hlen : i.val < a.val.length :=
        (List.getElem?_eq_some_iff.mp hsome).1
      simpa only [a.property] using hlen

theorem one_canonical :
    CanQ (toProbeQ AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE) := by
  change CanQ
    (AspisR1S9ActualQM31WrappingMapV1.toProbeQM
      (AspisR1S9ConstructorV3QMMulCanonicalV1.toActualQM
        AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE))
  simp only [AspisR1S9ActualQM31WrappingMapV1.toProbeQM,
    AspisR1S9ConstructorV3QMMulCanonicalV1.toActualQM,
    AspisR1S9ConstructorV3QMMulCanonicalV1.toActualCM,
    AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE]
  constructor <;> constructor <;> decide

theorem make4_cells_canonical
    (a b c d : Q)
    (ha : CanQ (toProbeQ a)) (hb : CanQ (toProbeQ b))
    (hc : CanQ (toProbeQ c)) (hd : CanQ (toProbeQ d)) :
    CellsCanonical (mapCells (Array.make 4#usize [a, b, c, d])) := by
  intro j v hread
  have hmap : mapCells (Array.make 4#usize [a, b, c, d]) =
      Array.make 4#usize [toProbeQ a, toProbeQ b, toProbeQ c, toProbeQ d] := rfl
  rw [hmap] at hread
  have hjbound := index_success_bound
    (Array.make 4#usize [toProbeQ a, toProbeQ b, toProbeQ c, toProbeQ d]) j v hread
  have hfour : (4#usize).val = 4 := by decide
  have hjcases : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by omega
  rcases hjcases with hj0 | hj1 | hj2 | hj3
  · have hj : j = 0#usize := UScalar.eq_of_val_eq (by simpa using hj0)
    subst j
    change Result.ok (toProbeQ a) = Result.ok v at hread
    have hv : toProbeQ a = v := Result.ok.inj hread
    simpa only [hv] using ha
  · have hj : j = 1#usize := UScalar.eq_of_val_eq (by simpa using hj1)
    subst j
    change Result.ok (toProbeQ b) = Result.ok v at hread
    have hv : toProbeQ b = v := Result.ok.inj hread
    simpa only [hv] using hb
  · have hj : j = 2#usize := UScalar.eq_of_val_eq (by simpa using hj2)
    subst j
    change Result.ok (toProbeQ c) = Result.ok v at hread
    have hv : toProbeQ c = v := Result.ok.inj hread
    simpa only [hv] using hc
  · have hj : j = 3#usize := UScalar.eq_of_val_eq (by simpa using hj3)
    subst j
    change Result.ok (toProbeQ d) = Result.ok v at hread
    have hv : toProbeQ d = v := Result.ok.inj hread
    simpa only [hv] using hd

private theorem bind_success_inv {α β : Type} (m : Result α)
    (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- One actual successful row-cell iteration of `weights_new_loop1_loop0.body`
preserves canonicality of the written five-cell row. The row, products, and
success witnesses all come from the same generated body execution. The input
row contract is stated at its exact `index_mut_usize` witness so an enclosing
factor-array invariant can discharge it by the existing mutable-index spec. -/
theorem loop1_body_same_call_cell_row_canonical
    (k d : Std.Usize) (iter iterNext : R)
    (factors factorsOut : Factors) (x xOut : Q)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some d, iterNext))
    (hbody : AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1_loop0.body
      k iter factors x = .ok (.cont (iterNext, factorsOut, xOut)))
    (hx : CanQ (toProbeQ x))
    (hd : d.val < 5)
    (hinput : ∀ (i : Std.Usize) (old : Row) (back : Row → Factors),
      Array.index_mut_usize factors i = .ok (old, back) →
      ∀ (j : Std.Usize) (cell : Array ProbeQ (4#usize)),
        Array.index_usize (mapRow old) j = .ok cell → CellsCanonical cell) :
    ∃ (y q : Q) (i : Std.Usize) (old : Row) (back : Row → Factors)
      (rowOut : Row),
      AspisR1S9ActualWeightsNewBoxNewV3.double x = .ok y ∧
      AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.mul x y = .ok q ∧
      lift (Std.Usize.wrapping_add 3#usize k) = .ok i ∧
      Array.index_mut_usize factors i = .ok (old, back) ∧
      Array.update old d (Array.make 4#usize
        [AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE, x, y, q]) = .ok rowOut ∧
      AspisR1S9ActualWeightsNewBoxNewV3.double y = .ok xOut ∧
      CanQ (toProbeQ xOut) ∧
      factorsOut = back rowOut ∧
      ∀ (j : Std.Usize) (cell : Array ProbeQ (4#usize)),
        Array.index_usize (mapRow rowOut) j = .ok cell → CellsCanonical cell := by
  unfold AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1_loop0.body at hbody
  rw [hnext] at hbody
  simp only [bind_tc_ok] at hbody
  obtain ⟨y, hy, hbody⟩ := bind_success_inv
    (AspisR1S9ActualWeightsNewBoxNewV3.double x) _ _ hbody
  obtain ⟨q, hq, hbody⟩ := bind_success_inv
    (AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.mul x y) _ _ hbody
  obtain ⟨i, hi, hbody⟩ := bind_success_inv
    (lift (Std.Usize.wrapping_add 3#usize k)) _ _ hbody
  obtain ⟨mutPair, hm, hbody⟩ := bind_success_inv
    (Array.index_mut_usize factors i) _ _ hbody
  rcases mutPair with ⟨old, back⟩
  change (do
    let rowOut ← Array.update old d
      (Array.make 4#usize [AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE, x, y, q] : Cell)
    let xNext ← AspisR1S9ActualWeightsNewBoxNewV3.double y
    ok (ControlFlow.cont (iterNext, back rowOut, xNext) : ControlFlow (R × Factors × Q) Factors)) =
      ok (ControlFlow.cont (iterNext, factorsOut, xOut) : ControlFlow (R × Factors × Q) Factors) at hbody
  obtain ⟨rowOut, hu, hbody⟩ := bind_success_inv
    (Array.update old d
      (Array.make 4#usize [AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE, x, y, q] : Cell)) _ _ hbody
  obtain ⟨xNext, hxNext, hbody⟩ := bind_success_inv
    (AspisR1S9ActualWeightsNewBoxNewV3.double y) _ _ hbody
  have hstate := ControlFlow.cont.inj (Result.ok.inj hbody)
  have hxEq : xNext = xOut := congrArg (fun s => s.2.2) hstate
  have hfEq : back rowOut = factorsOut := congrArg (fun s => s.2.1) hstate
  subst xOut
  subst factorsOut
  have hyCan :=
    AspisR1S9ConstructorV3DoubleCanonicalV1.generated_double_success_canonical
      x y hx hy
  have hqCan :=
    AspisR1S9ConstructorV3QMMulCanonicalV1.generated_mul_success_canonical
      x y q hx hyCan hq
  have hxNextCan :=
    AspisR1S9ConstructorV3DoubleCanonicalV1.generated_double_success_canonical
      y xNext hyCan hxNext
  have hcells := make4_cells_canonical
    AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE x y q
    one_canonical hx hyCan hqCan
  have hrowCan := hinput i old back hm
  have hrowOutCan :=
    AspisR1S9PairArrayUpdateCanonicalV1.update_preserves_canonical_reads
      mapCells CellsCanonical old d
      (Array.make 4#usize
        [AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE, x, y, q])
      rowOut hd hu hrowCan hcells
  exact ⟨y, q, i, old, back, rowOut, hy, hq, hi, hm, hu, hxNext,
    hxNextCan, rfl, hrowOutCan⟩

#print axioms loop1_body_same_call_cell_row_canonical

end AspisR1S9ConstructorV3Loop1CellCanonicalV1
