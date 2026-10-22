import R1LiteralQueryRead
import S4SourceByteOracleV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S4QueryArrayOrderV1

/-- The source array and decoded query coordinates retain the same order.
The list equality must come from the actual source scanner refinement. -/
theorem array_entry_eq_literal_query
    (out : Array U32 22#usize) (xs : List Nat)
    (q : Fin 22 → Fin 262144)
    (hdecode : LiteralQueryRead.decode xs = some q)
    (horder : out.val.map (fun x => x.val) = xs)
    (j : Fin 22) :
    (out.val[j.val]'(by scalar_tac)).val = (q j).val := by
  have hxs := (LiteralQueryRead.decode_success xs q hdecode).1
  have he : out.val.map (fun x => x.val) =
      List.ofFn (fun i : Fin 22 => (q i).val) := horder.trans hxs.symm
  have hj : j.val < out.val.length := by scalar_tac
  have hleft : (out.val.map (fun x => x.val))[j.val]? =
      some (out.val[j.val]'hj).val := by simp [hj]
  have hright : (List.ofFn (fun i : Fin 22 => (q i).val))[j.val]? =
      some (q j).val := by
    rw [List.getElem?_ofFn]
    simp only [dif_pos j.isLt]
  have hget := congrArg (fun ys : List Nat => ys[j.val]?) he
  rw [hleft, hright] at hget
  exact Option.some.inj hget

#print axioms array_entry_eq_literal_query
end AspisR1.S4QueryArrayOrderV1
