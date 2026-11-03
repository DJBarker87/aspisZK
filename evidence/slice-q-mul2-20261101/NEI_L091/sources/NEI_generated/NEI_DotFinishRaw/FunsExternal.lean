import NEI_DotFinishRaw.Types
import NEI_WideCtorRaw.Funs
open Aeneas Aeneas.Std Result
namespace NEI_DotFinishRaw
def wideFromRaw (x : NEI_WideCtorRaw.aspis_core.field.wide_exact.WideExact) :
 aspis_core.field.wide_exact.WideExact :=
 ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
  ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩
def aspis_core.field.wide_exact.WideExact.from_limbs (words : Array U32 8#usize) :
 Result (Option aspis_core.field.wide_exact.WideExact) := do
 let out ← NEI_WideCtorRaw.aspis_core.field.wide_exact.WideExact.from_limbs words
 ok (out.map wideFromRaw)
end NEI_DotFinishRaw
