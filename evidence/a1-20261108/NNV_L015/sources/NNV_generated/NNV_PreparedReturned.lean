import NNV_PreparedPorts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_PreparedReturned
open Aeneas Aeneas.Std Result NNH_Run5bCtx AspisR1CurrentCaller
open NNV_PreparedInputs
/-- The canonical P returned arm selects the actual emitted Result and scratch. -/
theorem model (s : RSL.Verified LIB_VLib.library) (v : LIB_VCarriers.View)
 (g : LIB_VCarriers.E29) (env : RSL.Env)
 (reply : Except LIB_VCarriers.VErr LIB_VCarriers.Prepared × LIB_VCarriers.E29)
 (events : List RSL.Event)
 (called : LIB_Prepared.child.law (s,v,g) env ⟨.ret reply,events⟩) :
 ∃ native, NGN_Emitted.prepared NHL_PreparedScalars.actual (LIBC_PreparedLog.digest env)
   (LIBC_PreparedCarriers.verified LIB_Prepared.types s) v () g = .ok native ∧
 reply = LIBC_PreparedLaw.port native := by
 obtain ⟨⟨exit,ev⟩,law,image⟩ := (LIB_Prepared.exact_graph (s,v,g) env _).mp called
 cases exit with
 | abort => cases congrArg RSL.Obs.exit image
 | diverge => cases congrArg RSL.Obs.exit image
 | ret out =>
  have same : reply = LIB_Prepared.output out := RSL.Exit.ret.inj (congrArg RSL.Obs.exit image)
  have normalized : LIB_Prepared.output out = out := by
   rcases out with ⟨out,g⟩
   cases out <;> rfl
  rw [normalized] at same
  obtain ⟨native,result,port,_⟩ := (LIBC_PreparedLaw.returned _ env out ev).mp law
  refine ⟨native,?_,same.trans port⟩
  exact (LIBC_PreparedLaw.native_result _ env).symm.trans result
#print axioms model
end AspisR1.NNV_PreparedReturned
end
