import NLJ_Control137
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Control137
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- CLOSED138 at the SAME bytes, including every outer/inner Result arm and
all root/record fields. No successful parse is assumed. -/
theorem parser (bytes : Slice U8) : parse bytes = PrefixAdapter.parseAccepted bytes := by
 unfold parse
 rw [←NGX_PrefixSource.source]
 unfold NGX_PrefixCarrier.result PrefixAdapter.parseAccepted
 generalize AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes = reply
 cases reply with
 | fail e => rfl
 | div => rfl
 | ok r =>
   cases r with
   | Ok p => rfl
   | Err e => cases e <;> rfl
#print axioms parser
end AspisR1.NLJ_Control137
end
