import GExq_OuterGoodLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_OuterGoodFirst
open Aeneas Aeneas.Std Result AdapterRw S2W_Trace S2W_Outer
open GExq_OuterLower GExq_OuterGoodLaws

theorem first_decoded (sdk : AdapterRw.Ops) (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : S2Z.Oracle.NativeBinding sdk hashv)
    (semantic : AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) :
    Good hashv (S2W_Outer.first_decoded sdk traceEffects semantic pub proof split) := by
  unfold S2W_Outer.first_decoded
  change Good hashv (perform (.op10 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 sdk)
    semantic pub proof split () none) >>= fun r => mapError (fun e => perform (.op44 e)) r)
  apply call_bind_good
  · exact ⟨law,rfl⟩
  · intro result
    cases result with
    | Ok x => exact pure_good _ _
    | Err e =>
      apply call_bind_good
      · trivial
      · intro error; exact pure_good _ _

#print axioms first_decoded
end AspisR1.GExq_OuterGoodFirst
end
