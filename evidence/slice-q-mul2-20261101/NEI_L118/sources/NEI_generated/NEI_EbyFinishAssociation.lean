import NEI_DotFinishAssociation
import NEI_WideCtorAssociation
set_option autoImplicit false
noncomputable section
namespace NEI_EbyFinishAssociation
open Aeneas Aeneas.Std Result
abbrev R := NEI_DotFinishRaw.aspis_core.field.wide_exact.WideExact
def toE (x : R) : FIo_Native.aspis_core.field.wide_exact.WideExact :=
 ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
  ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩
def toOuter (x : NEI_DotFinishRaw.fast_pairing.EbyKDot) : FIo_Native.fast_pairing.EbyKDot :=
 ⟨NEI_DotFinishAssociation.toD x.c0,NEI_DotFinishAssociation.toD x.c1,x.count⟩
private theorem associate {A B C : Type} (x : Result A) (f : A → Result B)
 (g : B → Result C) : ((x >>= f) >>= g)=(x >>= fun a=>f a >>= g) := by
 cases x <;> rfl
/-- Nominal transport preserves rejection/panic as well as each success field. -/
theorem ctor_unwrap (a b c d e f g h : U32) :
 (do let out ← NEI_DotFinishRaw.aspis_core.field.wide_exact.WideExact.from_limbs
       (Array.make 8#usize [a,b,c,d,e,f,g,h])
     let value ← core.option.Option.unwrap out;ok (toE value)) =
 (do let out ← FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs
       (Array.make 8#usize [a,b,c,d,e,f,g,h]);core.option.Option.unwrap out) := by
 rw [← NEI_WideCtorAssociation.same_result a b c d e f g h]
 unfold NEI_DotFinishRaw.aspis_core.field.wide_exact.WideExact.from_limbs
 cases run : NEI_WideCtorRaw.aspis_core.field.wide_exact.WideExact.from_limbs
       (Array.make 8#usize [a,b,c,d,e,f,g,h]) with
 | fail error => rfl
 | div => rfl
 | ok out => cases out <;> rfl
/-- Both full Result computations use identical children and argument carriers. -/
theorem same (x : NEI_DotFinishRaw.fast_pairing.EbyKDot) :
 (do let value ← NEI_DotFinishRaw.fast_pairing.EbyKDot.finish x;ok (toE value)) =
 FIo_Native.fast_pairing.EbyKDot.finish (toOuter x) := by
 simp only [NEI_DotFinishRaw.fast_pairing.EbyKDot.finish,
  FIo_Native.fast_pairing.EbyKDot.finish,associate,
  NEI_DotFinishAssociation.finish,NEI_DotFinishRaw.fast_pairing.canonical.Q.limbs,
  FIo_Native.fast_pairing.canonical.Q.limbs,toOuter,bind_tc_ok,ctor_unwrap]
#print axioms ctor_unwrap
#print axioms same
end NEI_EbyFinishAssociation
end
