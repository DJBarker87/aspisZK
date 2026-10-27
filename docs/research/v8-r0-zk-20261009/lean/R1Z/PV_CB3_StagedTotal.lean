import R1Z.PV_CB3_StagedSource
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_StagedTotal
open Aeneas Aeneas.Std Result ProverRwFull
open PV_CB3_StagedFields.aspis_core.field
/-- The canonical constructor retains complete Result semantics at raw inputs. -/
theorem constructor_total (a b : ProverRwFull.aspis_core.field.QM31) :
    ∃ x, wide_exact.WideExact.new a b = ok x := by
  simp [wide_exact.WideExact.new, wide_exact.canonical_qm31,
    wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
    ct.reduce64, ct.subtract_p, PV_CB3_StagedFields.aspis_core.field.P, lift, bind_tc_ok]
/-- Array reads are total at an in-bounds machine index. -/
theorem read_eq {T : Type} {n : Usize} (xs : Array T n) (i : Usize)
    (h : i.val < n.val) :
    Array.index_usize xs i = ok (xs.val[i.val]'(by simpa only [xs.property] using h)) := by
  change (match xs.val[i.val]? with | none => _ | some x => _) = _
  rw [List.getElem?_eq_getElem (by simpa only [xs.property] using h)]
#print axioms constructor_total
#print axioms read_eq
end R1Z.PV_CB3_StagedTotal
