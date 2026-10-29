import PV_B3P_SelectValue227
import PV_B3P_Select227
namespace PV_B3P_SelectD227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_SelectIndex227 PV_B3P_SelectValue227
set_option autoImplicit false

def view (claims : Claims) (row : Fin 3) (column : Fin 29) : aspis_core.field.QM31 :=
  let r := claims.val[row.val]'(by have h := claims.property; scalar_tac)
  r.val[column.val]'(by have h := r.property; scalar_tac)

theorem cell_as_select (claims : Claims) (i : Fin 84) :
    cell claims i.val i.isLt = PV_B3P_Select227.select (view claims) i := rfl

theorem expected_eq (a b : Claims)
    (h : ∀ r c, c.val < 28 → view a r c = view b r c) : expected a = expected b := by
  unfold expected
  apply congrArg List.ofFn
  funext i
  rw [cell_as_select a i,cell_as_select b i]
  exact congrFun (PV_B3P_Select227.omitted_D (view a) (view b) h) i

theorem array_eq {α : Type} {n : Usize} (a b : Array α n) (h : a.val=b.val) : a=b := by
  cases a
  cases b
  cases h
  rfl

theorem source_D (a b : Claims)
    (h : ∀ r c, c.val < 28 → view a r c = view b r c) :
    reference_terminal.select227 a = reference_terminal.select227 b := by
  obtain ⟨outa,ha,hva⟩ := PV_B3P_SelectValue227.nonvacuity a
  obtain ⟨outb,hb,hvb⟩ := PV_B3P_SelectValue227.nonvacuity b
  rw [ha,hb]
  apply congrArg Result.ok
  apply array_eq
  exact hva.trans ((expected_eq a b h).trans hvb.symm)

#print axioms cell_as_select
#print axioms expected_eq
#print axioms array_eq
#print axioms source_D
end PV_B3P_SelectD227
