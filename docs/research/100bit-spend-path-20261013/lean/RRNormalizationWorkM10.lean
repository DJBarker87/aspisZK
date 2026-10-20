import RRRowConstructionWorkM10
import RRConcreteState

/-! Construction, full scanner and reconstruction of a raw normalized child.
Both row grids are paid: the scan grid is not confused with the separately
rebuilt runtime grid. Stored widths, rather than semantic degree, bound work. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RRNormalizationWorkM10
open CompPoly RRConcreteState RRRowConstructionWorkM10
variable {K : Type} [Field K] [DecidableEq K]

def rows (D : Nat) (gs : List (List K)) (a : K) (M B : Nat) : List (List K) × Nat :=
  let r := (List.finRange (B+1)).map (fun n => RRRowConstructionWorkM10.row D gs a M n.val)
  (r.map Prod.fst,(r.map Prod.snd).sum+3*(B+1)+1)

theorem rows_value (D : Nat) (gs : List (List K)) (a : K) (M B : Nat) :
    (rows D gs a M B).1 = RRVectorNormalizedRows.rowsThrough gs a M B := by
  simp only [rows, List.map_map, Function.comp_def, row_value,
    RRVectorNormalizedRows.rowsThrough, List.ofFn_eq_map]

def rowBudget (D : Nat) : Nat := (D+1)*(D*termTariff D+2*D+6)+D+2

theorem rows_work (D : Nat) (gs : List (List K)) (a : K) (M B : Nat)
    (hB : B ≤ D) (hw : ∀ r ∈ gs, r.length ≤ D) :
    (rows D gs a M B).2 ≤ (D+1)*(rowBudget D+3)+1 := by
  have h := RawExtractorCostLedger.sum_charge_le (List.finRange (B+1))
    (fun n => (RRRowConstructionWorkM10.row D gs a M n.val).2)
    (B+1) (rowBudget D) (by simp)
    (fun n _ => row_work D gs a M n.val (by have hn := n.isLt; omega) hw)
  have hm := Nat.mul_le_mul_right (rowBudget D+3) (Nat.add_le_add_right hB 1)
  change _+3*(B+1)+1 ≤ _
  simp only [List.map_map, Function.comp_def] at *
  calc
    _ ≤ (B+1)*rowBudget D+3*(B+1)+1 := by omega
    _ = (B+1)*(rowBudget D+3)+1 := by ring
    _ ≤ _ := Nat.add_le_add_right hm 1

def scan : List (List K) → Option (Nat × List K) × Nat
  | [] => (none,1)
  | row::rest =>
    let later := scan rest
    (if RRFiniteCoeffScannerV9.rowNonzeroFull row then some (0,row)
      else later.1.map (fun x => (x.1+1,x.2)),later.2+row.length+3)

theorem scan_value (gs : List (List K)) :
    (scan gs).1 = RRFiniteCoeffScannerV9.firstNonzeroFullRows gs := by
  induction gs with
  | nil => rfl
  | cons row rest ih =>
    simp only [scan, RRFiniteCoeffScannerV9.firstNonzeroFullRows, ih]

theorem scan_work (gs : List (List K)) :
    (scan gs).2 = GSStoredRowsEnvelopeM10.slots gs+3*gs.length+1 := by
  induction gs with
  | nil => simp [scan, GSStoredRowsEnvelopeM10.slots]
  | cons row rest ih =>
    simp only [scan, ih, GSStoredRowsEnvelopeM10.slots, List.map_cons, List.sum_cons,
      List.length_cons]
    ring

def normalize (D ell : Nat) (s : RawState K) (a : K) : Option (RawState K) × Nat :=
  let grid := rows D s.rows a s.maxX ell
  let found := scan grid.1
  match found.1 with
  | none => (none,grid.2+found.2+4)
  | some (v,_) =>
    let full := rows D s.rows a s.maxX (s.maxX+ell)
    (some ⟨full.1.drop v,s.maxX+ell-v⟩,
      grid.2+found.2+full.2+(s.maxX+ell+1)+8)

theorem normalize_value (D ell : Nat) (s : RawState K) (a : K) :
    (normalize D ell s a).1 = normalizeChild? ell s a := by
  simp only [normalize, rows_value, scan_value, normalizeChild?,
    RRVectorActualScanner.rowsUpTo, RRVectorNormalizedRows.rowsThrough,
    RRFiniteRootSamplerNormalizedStateBridge.normalizedRuntimeState,
    RRRuntimeNormalizedChildReconstruction.runtimeRows]
  split <;> rename_i h <;> simp only [h]

def budget (D : Nat) : Nat :=
  2*((D+1)*(rowBudget D+3)+1)+(D+1)^2+4*(D+1)+32

theorem normalize_work (D ell : Nat) (s : RawState K) (a : K)
    (hD : s.maxX+ell ≤ D) (hw : ∀ r ∈ s.rows, r.length ≤ D) :
    (normalize D ell s a).2 ≤ budget D := by
  have he : ell ≤ D := by omega
  have hg := rows_work D s.rows a s.maxX ell he hw
  have hf := rows_work D s.rows a s.maxX (s.maxX+ell) hD hw
  have hslots : GSStoredRowsEnvelopeM10.slots (rows D s.rows a s.maxX ell).1 ≤ (D+1)^2 := by
    rw [rows_value, pow_two]
    apply GSStoredRowsEnvelopeM10.slots_bound _ (D+1) (D+1)
    · rw [GSStoredRowsEnvelopeM10.rowsThrough_length]; omega
    · intro row hr
      exact (GSStoredRowsEnvelopeM10.rowsThrough_width _ _ _ _ row hr).trans (by omega)
  have hs := scan_work (rows D s.rows a s.maxX ell).1
  have hlen : (rows D s.rows a s.maxX ell).1.length = ell+1 := by
    rw [rows_value, GSStoredRowsEnvelopeM10.rowsThrough_length]
  simp only [normalize]
  split <;> dsimp only <;> unfold budget <;> omega

#print axioms rows_value
#print axioms rows_work
#print axioms scan_value
#print axioms scan_work
#print axioms normalize_value
#print axioms normalize_work
end AspisR1.RRNormalizationWorkM10
end
