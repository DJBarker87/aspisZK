import NNG_PreparedGraph087
import NNG_ReadyView087
import NNG_FrontProjection087
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_PreparedOccurrence087
open Aeneas Aeneas.Std Result NMP_prepare NMT_CallTree NNG_Observed136
open NMT_Transport (arr)
abbrev Args:=NNG_PrepareInput087.Args

theorem output_identity (o : RSL.Obs LIBC_PreparedLaw.Output) :
 LIBC_SpecMap.observation LIB_Prepared.output o=o := by
 rcases o with ⟨exit,events⟩
 cases exit with
 | abort=>rfl
 | diverge=>rfl
 | ret r=>
  rcases r with ⟨r,g⟩
  cases r <;> rfl
#print axioms output_identity

theorem input_exact (a : Args) (obs : RSL.Observer) (env : RSL.Env)
 (sem : r1_semantic.Verified Unit) (v : verifier.View) (ready : NNG_ReadyView087.Ready sem v) :
 LIB_Prepared.input (NNG_FrontProjection087.verified a env v sem,NNG_PrepareCarriers087.view v,a.g)=
 (NMP_Transport.toT11 sem,NNG_PrepareCarriers087.view v,
   arr NNG_PrepareCarriers087.wide (NNG_PrepareInput087.input a obs env).scratch) := by
 have lowering:=NNG_VerifiedRoundtrip136.verified
  (NNG_Data137.fallback (NNG_ObservedInput087.child a v) env) (NNG_Output137.verified sem) ready.1
 simp only [NNG_Output137.verified,NNG_Transport.fromT11_inverse] at lowering
 change (LIBC_PreparedCarriers.verified LIB_Prepared.types (NNG_FrontProjection087.verified a env v sem),NNG_PrepareCarriers087.view v,a.g)=_
 exact congrArg₂ Prod.mk lowering
  (congrArg (Prod.mk (NNG_PrepareCarriers087.view v)) (NNG_PrepareInput087.scratch_exact a obs env).symm)

#print axioms input_exact

theorem occurrence (a : Args) (obs : RSL.Observer) (env : RSL.Env)
 (sem : r1_semantic.Verified Unit) (v : verifier.View) (ready : NNG_ReadyView087.Ready sem v) :
 LIB_Prepared.child.run (NNG_FrontProjection087.verified a env v sem,NNG_PrepareCarriers087.view v,a.g) env
 (observation NNG_PreparedCall087.port (NNG_Events087.events env)
  (invoke "TX1:179/Prepared_new" (sem,v,(),(NNG_PrepareInput087.input a obs env).scratch)
   (NNG_PreparedCall087.call (NNG_PublicSource137.digest env) sem v () (NNG_PrepareInput087.input a obs env).scratch))) := by
 have inputEq:=input_exact a obs env sem v ready
 have dom : LIBC_PreparedDomain.Domain
  (NMP_Transport.toT11 sem,NNG_PrepareCarriers087.view v,
   arr NNG_PrepareCarriers087.wide (NNG_PrepareInput087.input a obs env).scratch) := by
  exact ready.2
 refine ⟨?_,?_⟩
 · apply LIB_Prepared.caller_clauses _ |>.mpr
   exact Eq.mp (congrArg LIBC_PreparedDomain.Domain inputEq.symm) dom
 · apply (LIB_Prepared.exact_graph _ env _).mpr
   refine ⟨observation NNG_PreparedCall087.port (NNG_Events087.events env)
    (invoke "TX1:179/Prepared_new" (sem,v,(),(NNG_PrepareInput087.input a obs env).scratch)
     (NNG_PreparedCall087.call (NNG_PublicSource137.digest env) sem v () (NNG_PrepareInput087.input a obs env).scratch)),?_,?_⟩
   · exact Eq.mp (congrArg (fun args=>LIBC_PreparedLaw.law args env _) inputEq.symm)
      (NNG_PreparedGraph087.law env sem v (NNG_PrepareInput087.input a obs env).scratch)
   · exact (output_identity _).symm
#print axioms occurrence
end AspisR1.NNG_PreparedOccurrence087
