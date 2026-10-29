import NDN_Reference2.Funs
import NDN_Reference5.Funs
import NDN_Reference20.Funs
import NDE_VariantBridge
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDN_AddWordBridge

theorem word (a b : U32) :
    NDN_Reference20.add_word a b=FIq_Native.field.M31.add a b := by
  change NDE_Reference3.add_word_ref a b=FIq_Native.field.M31.add a b
  exact NDE_VariantBridge.word_reference a b

theorem active (a b : U32) (selected : Bool) :
    NDN_Reference2.active_high_word a b selected =
      if selected then FIq_Native.field.M31.add a b else ok a := by
  cases selected
  · rfl
  · change NDN_Reference20.add_word a b=FIq_Native.field.M31.add a b
    exact word a b

theorem pattern (a b : U32) (selected : Bool) :
    NDN_Reference5.pattern_word a b selected =
      if selected then FIq_Native.field.M31.add a b else ok a := by
  cases selected
  · rfl
  · change NDN_Reference20.add_word a b=FIq_Native.field.M31.add a b
    exact word a b

#print axioms word
#print axioms active
#print axioms pattern
end NDN_AddWordBridge
