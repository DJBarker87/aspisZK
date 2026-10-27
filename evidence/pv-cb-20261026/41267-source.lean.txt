import R1Z.PV_CB_MaskHorner
import R1Z.ProverRwP6ArrayRead
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_HornerCell
open Aeneas Aeneas.Std Result
abbrev Q := ProverRwFull.aspis_core.field.QM31
abbrev Coeff := Array Q 27#usize
abbrev Prepared := PV_CB_PreparedTotal.Prepared
def scalar (p : Prepared) (shared coefficient : Q) : Result Q := do
  let product ← PV_CB_MaskHorner.S.mul p shared
  PV_CB_MaskHorner.S.add product coefficient
def cell (coeff : Coeff) (p : Prepared) (i : Usize) (shared : Q) : Result Q := do
  let product ← PV_CB_MaskHorner.S.mul p shared
  let coefficient ← coeff.index_usize i
  PV_CB_MaskHorner.S.add product coefficient
theorem read (coeff : Coeff) (p : Prepared) (i : Usize) (shared value : Q)
    (h : coeff.index_usize i = ok value) :
    cell coeff p i shared = scalar p shared value := by
  simp only [cell,scalar,h,bind_tc_ok]
theorem locality (left right : Coeff) (p : Prepared) (i : Usize) (shared : Q)
    (h : left.index_usize i = right.index_usize i) :
    cell left p i shared = cell right p i shared := by
  simp only [cell,h]
theorem scalar_representative (coeff : Coeff) (p : Prepared) (i : Usize) (shared : Q)
    (inside : i.val<27) :
    ∃ value, cell coeff p i shared = scalar p shared value := by
  obtain ⟨value,h⟩ := ProverRwP6ArrayRead.read coeff i inside
  exact ⟨value,read coeff p i shared value h⟩
#print axioms read
#print axioms locality
#print axioms scalar_representative
end R1Z.PV_CB_HornerCell
