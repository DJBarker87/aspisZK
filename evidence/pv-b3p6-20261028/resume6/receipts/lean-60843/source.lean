import PV_B3P_SelectEmission227
namespace PV_B3P_SelectIndex227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

abbrev Claims := Array (Array aspis_core.field.QM31 29#usize) 3#usize

def cell (claims : Claims) (i : Nat) (hi : i < 84) : aspis_core.field.QM31 :=
  let row := claims.val[i / 28]'(by have h := claims.property; scalar_tac)
  row.val[i % 28]'(by have h := row.property; scalar_tac)

theorem index_value {α : Type} {n : Usize} (xs : Array α n) (i : Usize)
    (hi : i.val < n.val) :
    Array.index_usize xs i = .ok (xs.val[i.val]'(by simpa [xs.property] using hi)) := by
  have hlen : i.val < xs.val.length := by simpa [xs.property] using hi
  unfold Array.index_usize
  change (match xs.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (xs.val[i.val]'hlen)
  rw [List.getElem?_eq_getElem hlen]

theorem claim_value (claims : Claims) (i : Usize) (hi : i.val < 84) :
    reference_terminal.claim227 claims i = .ok (cell claims i.val hi) := by
  obtain ⟨q,hq,hqval⟩ := UScalar.div_spec (x:=i) (y:=28#usize) (by decide)
  obtain ⟨r,hr,hrval⟩ := WP.spec_imp_exists
    (UScalar.rem_spec (x:=i) (y:=28#usize) (by decide))
  have hqnat : q.val = i.val / 28 := by simpa using hqval
  have hrnat : r.val = i.val % 28 := by simpa using hrval
  have hqb : q.val < (3#usize).val := by change q.val < 3; omega
  have hrb : r.val < (29#usize).val := by change r.val < 29; omega
  unfold reference_terminal.claim227
  rw [hq]
  simp only [bind_tc_ok]
  rw [index_value claims q hqb]
  simp only [bind_tc_ok]
  rw [hr]
  simp only [bind_tc_ok]
  rw [index_value _ r hrb]
  simp only [cell,hqnat,hrnat]

#print axioms index_value
#print axioms claim_value
end PV_B3P_SelectIndex227
