import S1FinishFromFnStableV1
import S1SemanticFinishModelV1
set_option autoImplicit false
namespace AspisS1FinishSelectors
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
abbrev Q := aspis_core.field.QM31
abbrev Claims := Array (Array Q 29#usize) 3#usize

def cell (claims : Claims) (i : Nat) : Q :=
  (claims.val[0]'(by simpa [claims.property])).val[i % 29]'(by
    have bound : i % 29 < 29 := Nat.mod_lt _ (by decide)
    simpa [((claims.val[0]'(by simpa [claims.property])).property)] using bound)

private theorem index_ok {T : Type} {n : Usize} (a : Array T n) (i : Usize)
    (hi : i.val < n.val) :
    Array.index_usize a i = ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  unfold Array.index_usize
  change (match a.val[i.val]? with | none => fail Error.arrayOutOfBounds | some x => ok x) = _
  rw [List.getElem?_eq_getElem (by simpa [a.property] using hi)]

theorem first_callback {H : Type} (D : aspis_core.Digest32 H)
    (claims : Claims) (i : Usize) (hi : i.val < 16) :
    (FinishModel.closureFn9 D).call_mut claims i = ok (cell claims i.val,claims) := by
  have row := index_ok claims 0#usize (by decide)
  have col := index_ok (claims.val[0]'(by simpa [claims.property])) i (by change i.val < 29; omega)
  change (do
    let a ← Array.index_usize claims 0#usize
    let q ← Array.index_usize a i
    ok (q,claims)) = _
  rw [row,bind_tc_ok]
  change (do
    let q ← Array.index_usize (claims.val[0]'(by simpa [claims.property])) i
    ok (q,claims)) = _
  rw [col,bind_tc_ok]
  simp only [cell,Nat.mod_eq_of_lt (show i.val < 29 by omega)]

theorem second_callback {H : Type} (D : aspis_core.Digest32 H)
    (claims : Claims) (i : Usize) (hi : i.val < 10) :
    (FinishModel.closureFn5 D).call_mut claims i = ok (cell claims (16+i.val),claims) := by
  obtain ⟨j,add,hj⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x:=16#usize) (y:=i) (by scalar_tac))
  have jval : j.val = 16+i.val := by simpa using hj
  have row := index_ok claims 0#usize (by decide)
  have col := index_ok (claims.val[0]'(by simpa [claims.property])) j (by change j.val < 29; omega)
  change (do
    let j ← 16#usize+i
    let a ← Array.index_usize claims 0#usize
    let q ← Array.index_usize a j
    ok (q,claims)) = _
  rw [add,bind_tc_ok,row,bind_tc_ok]
  change (do
    let q ← Array.index_usize (claims.val[0]'(by simpa [claims.property])) j
    ok (q,claims)) = _
  rw [col,bind_tc_ok]
  simp only [cell,Nat.mod_eq_of_lt (show 16+i.val < 29 by omega),jval]

/-- TOTAL selector model, on arbitrary complete raw coefficient words. The
callback state and every output entry are derived; callback success is not
an additional caller premise. Native library correspondence is checked at
these two source expressions in the companion Kani packet. -/
theorem first_total {H : Type} (D : aspis_core.Digest32 H) (claims : Claims) :
    ∃ out : Array Q 16#usize,
      AspisR1SelectedMaskProbe.core.array.from_fn 16#usize (FinishModel.closureFn9 D) claims = ok out ∧
      out.val = (List.range 16).map (cell claims) := by
  obtain ⟨out,call,values⟩ := AspisR1SelectedMaskProbe.finish_from_fn_total_of_stable
    16#usize (FinishModel.closureFn9 D) (cell claims) claims
    (fun i hi => first_callback D claims i hi)
  exact ⟨out,call,by simpa using values⟩

theorem second_total {H : Type} (D : aspis_core.Digest32 H) (claims : Claims) :
    ∃ out : Array Q 10#usize,
      AspisR1SelectedMaskProbe.core.array.from_fn 10#usize (FinishModel.closureFn5 D) claims = ok out ∧
      out.val = (List.range 10).map (fun i => cell claims (16+i)) := by
  obtain ⟨out,call,values⟩ := AspisR1SelectedMaskProbe.finish_from_fn_total_of_stable
    10#usize (FinishModel.closureFn5 D) (fun i => cell claims (16+i)) claims
    (fun i hi => second_callback D claims i hi)
  exact ⟨out,call,by simpa using values⟩

#print axioms first_callback
#print axioms second_callback
#print axioms first_total
#print axioms second_total
end AspisS1FinishSelectors
