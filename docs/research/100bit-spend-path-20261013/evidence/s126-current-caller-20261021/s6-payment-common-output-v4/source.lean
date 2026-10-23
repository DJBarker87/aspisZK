import S6SourcePaymentCommonContentsV1
import S6SourcePaymentCommonEncodeTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6SourceCodec.PaymentContents
open AspisS6FiveUnrolledCodec
open aspis_statement.pool_v1.payment_relation

/-- Existential form of the symbolic writer contract. Keeping the full source
function beneath equality avoids normalizing its concrete header application. -/
theorem common_output (initial : Array U8 216#usize) (magic : Array U8 4#usize)
    (kind : aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind)
    (common : CommonPublicV1) :
    ∃ output, encode_common initial magic kind common=ok output ∧
      (initial=Array.repeat 216#usize 0#u8 → output.val=common_prefix magic kind common++List.replicate 68 0#u8) := by
  obtain ⟨output,houtput⟩ := PaymentEncodeTotal.common_write_total
    initial magic kind common
  have contents : encode_common initial magic kind common
      ⦃ output => initial=Array.repeat 216#usize 0#u8 → output.val=common_prefix magic kind common++List.replicate 68 0#u8 ⦄ :=
    common_contents initial magic kind common
  rw [houtput,WP.spec_ok] at contents
  exact ⟨output,houtput,contents⟩

#print axioms common_output
end AspisS6SourceCodec.PaymentContents
