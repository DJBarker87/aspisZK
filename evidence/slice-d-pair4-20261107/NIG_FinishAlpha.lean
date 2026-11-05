import NIG_FinishConcrete
import NHI_ScalarDomain
set_option autoImplicit false
namespace NIG_FinishAlpha
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 LPi_FieldValues
abbrev E:=aspis_core.field.wide_exact.WideExact

theorem canonical (x:E) (h:NBO_TailDomain.WideCanonical x):canonE (FIo_Install.toE x):=by
 rcases h with ⟨h0,h1⟩
 exact ⟨⟨⟨h0 0,h0 1⟩,⟨h0 2,h0 3⟩⟩,⟨⟨h1 0,h1 1⟩,⟨h1 2,h1 3⟩⟩⟩

def alpha (p:verifier.Prepared) (i:Nat) (h:i<2):E:=
 NHI_ScalarDomain.pick p.alpha i h

theorem selected (proof:Slice U8) (v:verifier.View) (p:verifier.Prepared)
 (a:verifier.Accumulator) (domain:NIG_FinishInput.Domain proof v p a)
 (i:Usize) (h:i.val<2):
 Array.index_usize p.alpha i=ok (alpha p i.val h) ∧
 canonE (FIo_Install.toE (alpha p i.val h)):=by
 refine ⟨NHI_ScalarDomain.index p.alpha i h,canonical _ ?_⟩
 apply domain.alpha i.val h
 simp [alpha,NHI_ScalarDomain.pick,show i.val<p.alpha.val.length by rw [p.alpha.property];exact h]

#print axioms canonical
#print axioms selected
end NIG_FinishAlpha
