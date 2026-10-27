import RPz7_S6NativeWordSourceBindingV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
open scoped AspisR1TerminalDecoder
namespace AspisS6NativeDigestDecodeBinding
open AspisR1TerminalDecoder

theorem option_eq {T E : Type} (value : Option T) (error : E) :
    core.option.Option.ok_or value error=AspisS6StdOptionMethods.option_ok_or value error := by
  cases value <;> rfl

@[step] theorem option_binding_spec {T E : Type} (value : Option T) (error : E) :
    core.option.Option.ok_or value error
      ⦃ result => ∀ x, result=core.result.Result.Ok x → value=some x ⦄ := by
  rw [option_eq]
  exact AspisS6SourceCodec.DigestRoundtrip.option_binding_spec value error

@[step] theorem decode_spec (bytes : Array U8 32#usize) :
    atomic_statement.decode_digest_canonical bytes ⦃ _ => True ⦄ := by
  unfold atomic_statement.decode_digest_canonical
  step*

#print axioms option_eq
#print axioms option_binding_spec
#print axioms decode_spec
end AspisS6NativeDigestDecodeBinding
