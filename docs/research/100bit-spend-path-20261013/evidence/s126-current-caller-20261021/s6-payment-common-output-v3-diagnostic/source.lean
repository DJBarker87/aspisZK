import S6SourcePaymentCommonContentsV1
import S6SourcePaymentCommonEncodeTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6SourceCodec.PaymentContents
open AspisS6FiveUnrolledCodec
open aspis_statement.pool_v1.payment_relation

/-- Existential form of the symbolic writer contract. Keeping the full source
function beneath equality avoids normalizing its concrete header application. -/
set_option diagnostics true in
theorem common_output (magic : Array U8 4#usize)
    (kind : aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind)
    (common : CommonPublicV1) :
    ∃ output, encode_common (Array.repeat 216#usize 0#u8) magic kind common=ok output ∧
      output.val=common_prefix magic kind common++List.replicate 68 0#u8 := by
  obtain ⟨output,houtput⟩ := PaymentEncodeTotal.common_write_total
    (Array.repeat 216#usize 0#u8) magic kind common
  have contents : encode_common (Array.repeat 216#usize 0#u8) magic kind common
      ⦃ output => output.val=common_prefix magic kind common++List.replicate 68 0#u8 ⦄ :=
    common_contents magic kind common
  rw [houtput,WP.spec_ok] at contents
  exact ⟨output,houtput,contents⟩

#print axioms common_output
end AspisS6SourceCodec.PaymentContents
