import PV_L2C_DecodeRange
import R1Z.PV_RunJoin_DecoderReturn29
set_option autoImplicit false
namespace PV_L2C_DigestRange
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

theorem scalar_eq (bytes : Array U8 4#usize) :
    aspis_core.field.M31.from_le_bytes bytes =
      PV_CB_ShippedOp71.aspis_core.field.M31.from_le_bytes bytes := rfl
#print axioms scalar_eq

theorem scalar_success (bytes : Array U8 4#usize) (v : U32)
    (h : aspis_core.field.M31.from_le_bytes bytes = ok (some v)) :
    v.val < 2147483647 :=
  PV_L2C_DecodeRange.scalar_success bytes v ((scalar_eq bytes).symm.trans h)
#print axioms scalar_success

theorem ok_or_return {T E : Type} (o : Option T) (e : E) (v : T)
    (h : core.option.Option.ok_or o e = ok (.Ok v)) : o = some v := by
  cases o with
  | none => cases h
  | some a => cases h; rfl
#print axioms ok_or_return

/-- Each returned limb of the actual eight-limb digest decoder is canonical.
This is success reflection, with no re-encoding premise. -/
theorem digest_success (bytes : Array U8 32#usize) (d : Array U32 8#usize)
    (h : atomic_statement.decode_digest_canonical bytes = ok (.Ok d)) :
    ∀ x ∈ d.val, x.val < 2147483647 := by
  unfold atomic_statement.decode_digest_canonical at h
  repeat' first
    | (have ho := ok_or_return _ _ _ hvalue; clear hvalue; cases ho)
    | (have hr := R1Z.PV_RunJoin_DecoderReturn29.branch_continue _ _ hvalue
       clear hvalue
       cases hr)
    | (pv_peel h with value hvalue; pv_head h)
    | (have _test : Option U32 := value; cases value <;> pv_head h)
    | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value)
    | exact False.elim (R1Z.PV_Src_ResultControl.error_ne_ok _ _ h)
    | exact False.elim (R1Z.PV_Src_ResultControl.same_residual_ne_ok _ _ h)
  all_goals
    cases h
    intro x hx
    simp only [Array.make, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx | hx | hx | hx | hx | hx | hx
    all_goals subst x; exact scalar_success _ _ (by assumption)
#print axioms digest_success
end PV_L2C_DigestRange
