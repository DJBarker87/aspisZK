import TerminalStandardOperationModelsV1

/-! Exact generic slice of the current `terminal_qm31` generated callback.

The source callback at current generated `Funs.lean` lines 2086:48–2086:74
does `claims[i / 28][i % 28]` and returns the same captured `claims` state.
This slice replaces only the concrete QM31 element type by a parameter, so
the callback body and fixed `[3][29]` array shape are unchanged. -/
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1SelectedMaskProbe

abbrev TerminalClaimsClosure (T : Type) := Array (Array T 29#usize) 3#usize

def terminalClaimsCallMut {T : Type} (c : TerminalClaimsClosure T)
    (tupled_args : Usize) : Result (T × TerminalClaimsClosure T) := do
  let i ← tupled_args / 28#usize
  let i1 ← tupled_args % 28#usize
  let a ← Array.index_usize c i
  let q ← Array.index_usize a i1
  ok (q, c)

private theorem array_index_usize_ok {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (hi : i.val < n.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

/-- The actual terminal callback is successful and state-preserving at every
flat cell below 84, with the row-major cell value. -/
theorem terminalClaimsCallMut_stable
    {T : Type} (c : TerminalClaimsClosure T) (flat : Usize)
    (hflat : flat.val < 84) :
    ∃ q, terminalClaimsCallMut c flat = .ok (q, c) ∧
      q = (c.val[flat.val / 28]'(by
        have hquot : flat.val / 28 < 3 := by omega
        simpa [c.property] using hquot)).val[flat.val % 28]'(by
        have hrow : flat.val / 28 < 3 := by omega
        have hrowIndex : flat.val / 28 < c.val.length := by
          simpa [c.property] using hrow
        have hcol : flat.val % 28 < 28 := Nat.mod_lt _ (by omega)
        have h29 : (29#usize : Usize).val = 29 := by scalar_tac
        have hrowLength : (c.val[flat.val / 28]'hrowIndex).val.length = 29 := by
          simpa [(c.val[flat.val / 28]'hrowIndex).property, h29]
        rw [hrowLength]
        omega) := by
  have h28 : (28#usize : Usize).val = 28 := by scalar_tac
  have hden : (28#usize : Usize).val ≠ 0 := by rw [h28]; omega
  obtain ⟨row, hdiv, hdivVal⟩ := @UScalar.div_spec .Usize flat (28#usize) hden
  have hmodSpec := UScalar.rem_spec flat (y := 28#usize) hden
  obtain ⟨col, hmodWp, hmodVal⟩ := Aeneas.Std.WP.spec_imp_exists hmodSpec
  have hrow : row.val < 3 := by rw [hdivVal, h28]; omega
  have hcol : col.val < 28 := by rw [hmodVal, h28]; exact Nat.mod_lt _ (by omega)
  have hquot : flat.val / 28 < 3 := by
    calc flat.val / 28 = row.val := by simpa [h28] using hdivVal.symm
      _ < 3 := hrow
  have hrem : flat.val % 28 < 28 := by
    calc flat.val % 28 = col.val := by simpa [h28] using hmodVal.symm
      _ < 28 := hcol
  have h3 : (3#usize : Usize).val = 3 := by scalar_tac
  have h29 : (29#usize : Usize).val = 29 := by scalar_tac
  have hrowIndex : flat.val / 28 < c.val.length := by
    have h3q : (3#usize : Usize).val = 3 := by scalar_tac
    rw [c.property, h3q]
    exact hquot
  let rowArray := c.val[flat.val / 28]'hrowIndex
  have hrowRead := array_index_usize_ok c row (by rw [h3]; exact hrow)
  have hquotEq : row.val = flat.val / 28 := by
    simpa only [h28] using hdivVal
  have hrowRead' : Array.index_usize c row = .ok rowArray := by
    simpa only [rowArray, hquotEq] using hrowRead
  have h29 : (29#usize : Usize).val = 29 := by scalar_tac
  have hcolBound : flat.val % 28 < rowArray.val.length := by
    have hb : flat.val % 28 < 29 := by omega
    simpa [rowArray.property, h29] using hb
  have hcolRead := array_index_usize_ok rowArray col (by
    rw [h29]
    omega)
  have hcolRead' : Array.index_usize rowArray col =
      .ok (rowArray.val[flat.val % 28]'hcolBound) := by
    simpa only [h28, hmodVal] using hcolRead
  refine ⟨rowArray.val[flat.val % 28]'hcolBound, ?_, rfl⟩
  simp only [terminalClaimsCallMut, hdiv, hmodWp, bind_tc_ok, hrowRead', hcolRead']

#print axioms terminalClaimsCallMut
#print axioms terminalClaimsCallMut_stable

end AspisR1SelectedMaskProbe
