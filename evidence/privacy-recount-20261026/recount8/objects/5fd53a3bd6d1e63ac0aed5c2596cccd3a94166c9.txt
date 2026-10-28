import R1Z.PV_Join_CanonicalArray5
set_option autoImplicit false
namespace R1Z.PV_Join_ArrayInvariant5
open Aeneas Aeneas.Std Result ProverRwFull PV_Join_Canonical5

theorem array_set {n : Usize} (xs : Array aspis_core.field.QM31 n)
    (hx : QArray xs) (i : Usize) (q : aspis_core.field.QM31) (hq : Q q) :
    QArray (Aeneas.Std.Array.set xs i q) :=
  PV_Join_CanonicalArray5.list_set xs.val hx i.val q hq

theorem update {n : Usize} (xs : Array aspis_core.field.QM31 n)
    (hx : QArray xs) (i : Usize) (q : aspis_core.field.QM31) (hq : Q q)
    (ys : Array aspis_core.field.QM31 n) (success : Array.update xs i q = .ok ys) :
    QArray ys := by
  unfold Array.update at success
  split at success
  · cases success
  · cases success
    exact array_set xs hx i q hq

theorem read {n : Usize} (xs : Array aspis_core.field.QM31 n)
    (hx : QArray xs) (i : Usize) (q : aspis_core.field.QM31)
    (success : Array.index_usize xs i = .ok q) : Q q := by
  simp only [Array.index_usize,Array.getElem?_Usize_eq] at success
  split at success
  · cases success
  · rename_i value hget
    have hm := List.mem_of_getElem? hget
    cases success
    exact hx _ hm

#print axioms array_set
#print axioms update
#print axioms read
end R1Z.PV_Join_ArrayInvariant5
