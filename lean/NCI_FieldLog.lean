import LPf_BaseMultiply
set_option autoImplicit false
namespace AspisR1.NCI_FieldLog
open Aeneas Aeneas.Std Result

structure Entry where
  lhs : U32
  rhs : U32
  reply : U32

def Realized (log : Entry) : Prop :=
  FIo_Native.aspis_core.field.M31.mul log.lhs log.rhs = ok log.reply ∧
  log.reply.val=(log.lhs.val*log.rhs.val)%2147483647 ∧ log.reply.val<2147483647

-- The native window is parametric in every canonical logged reply. Select the
-- concrete emitted reply here, rather than asserting a nonlinear Kani assume.
theorem instantiate (lhs rhs : U32) : ∃ reply, Realized ⟨lhs,rhs,reply⟩ :=
  LPf_BaseMultiply.source lhs rhs
#print axioms instantiate
end AspisR1.NCI_FieldLog
