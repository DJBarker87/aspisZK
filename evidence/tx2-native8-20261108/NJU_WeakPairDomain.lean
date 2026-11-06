import NJF_Root
set_option autoImplicit false
namespace AspisR1.NJU_WeakPairDomain
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts

/-- Generalization of NIT_PairDomain.Domain: same carriers, quantifiers,
structural/canonical owner facts, but only length on the arbitrary raw message.
Every malformed-word abort prefix remains in the Result semantics. -/
structure Domain (w : W) (alpha : Array E 2#usize) (f : Slice U8) (kappa : E) : Prop where
 s2 : w.variant=FIo_Native.transport.Variant.S2
 factors : NHI_TensorOuterStep.Factors w
 extra : NHI_CellCanon.array w.extra
 alphas : canonical alpha
 size : f.val.length=2048
 kappa : canonE kappa

theorem of_original (w : W) (alpha : Array E 2#usize) (f : Slice U8) (kappa : E)
 (domain : NIT_PairDomain.Domain w alpha f kappa) : Domain w alpha f kappa :=
 ⟨domain.s2,domain.factors,domain.extra,domain.alphas,domain.words.1,domain.kappa⟩

#print axioms of_original
end AspisR1.NJU_WeakPairDomain
