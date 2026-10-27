import RPz7_S6OuterNativeHelpersV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6OuterNativeTotalCallees
open AspisS6OuterNativeOps

@[step] theorem digest_spec (digest : Array U32 8#usize) : nativeOps.digest digest ⦃ _ => True ⦄ := by
  change AspisR1TerminalDecoder.atomic_statement.encode_digest_canonical digest ⦃ _ => True ⦄
  obtain ⟨result,run,_⟩ := spec_imp_exists (AspisS6NativeSnapshotEncodeTotal.digest_spec digest)
  rw [run,WP.spec_ok]
  trivial

#print axioms digest_spec
end AspisS6OuterNativeTotalCallees
