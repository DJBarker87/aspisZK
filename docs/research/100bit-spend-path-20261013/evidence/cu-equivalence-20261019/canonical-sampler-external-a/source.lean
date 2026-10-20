import AspisR1CanonicalSampler.Types
set_option autoImplicit false
namespace AspisR1CanonicalSampler
open Aeneas Aeneas.Std Result
class Shared where
  lowDigits : Array U8 32#usize→Result (Array U32 8#usize × U32)
  addSmall : Array U32 8#usize→U32→Result (Bool × Array U32 8#usize)
  traceValue : U16→Usize→field.wide_exact.WideExact→Result Unit
  block {H : Type} (digest : Digest32 H) :
    transcript.Transcript H→U8→Slice U8→Result (Array U8 32#usize × transcript.Transcript H)
abbrev sampler.low_base_p_digits [Shared] := Shared.lowDigits
abbrev sampler.add_small_base_p [Shared] := Shared.addSmall
abbrev trace.value [Shared] := Shared.traceValue
abbrev transcript.Transcript.block [Shared] := @Shared.block _
#print axioms Shared
end AspisR1CanonicalSampler
