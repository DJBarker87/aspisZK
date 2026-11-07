import NNG_PreparedFacts094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_PreparedCopies094
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedScratchReachability
/-- Every successful branch copies the exact original semantic roots and
coordinates and the exact View variant into Prepared. -/
theorem copied (input : LIBC_PreparedLaw.Args) (env : RSL.Env)
 (p : LIB_VCarriers.Prepared) (g : LIB_VCarriers.E29) (ev : List RSL.Event)
 (returned : LIBC_PreparedLaw.law input env ⟨.ret (.ok p,g),ev⟩) :
 p.variant=input.2.1.variant ∧ p.roots=input.1.roots ∧
 p.semantic_alpha=input.1.alpha ∧ p.z=input.1.z := by
 have native := NNG_PreparedFacts094.emitted input env p g ev returned
 have model := (NGN_EmittedEq.source NHL_PreparedScalars.actual (LIBC_PreparedLog.digest env)
  input.1 input.2.1 () input.2.2).symm.trans native
 obtain ⟨start,t1,t2,t3,bytes,gamma,kappa,alpha0,hs,hg,hb,hk,ha,tail⟩ :=
  prepare_success _ (LIBC_PreparedLog.digest env) input.1 input.2.1 () p g input.2.2 model
 cases tail with
 | single hf rest =>
   obtain ⟨queries,aq,last,rho,claim,hq,hr,hp,hc,same⟩ := rest
   subst p
   exact ⟨rfl,rfl,rfl,rfl⟩
 | double hf root b1 b2 alpha1 afterAlpha hroot hb1 hb2 ha1 rest =>
   obtain ⟨queries,aq,last,rho,claim,hq,hr,hp,hc,same⟩ := rest
   subst p
   exact ⟨rfl,rfl,rfl,rfl⟩
#print axioms copied
end AspisR1.NNG_PreparedCopies094
