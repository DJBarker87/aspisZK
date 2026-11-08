import NNG_ReadyView087
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ViewPrefix094
open Aeneas Aeneas.Std Result NMP_prepare
abbrev Args := NNG_PrepareInput087.Args

theorem variant (proof semantic y1 : Slice U8) (bound : 10055≤proof.val.length) (v : verifier.View)
 (native : NNG_WideView087.call proof semantic y1=.ok (.Ok v)) : v.variant=.S2 := by
 obtain ⟨limbs,_,same⟩ := NNG_ViewShape087.shape proof semantic y1 bound v native
 rw [same]
 rfl
#print axioms variant

/-- The SAME View returned through the observed call keeps the expanded
semantic backing, rather than an independently chosen prefix. -/
theorem returned (a : Args) (obs : RSL.Observer) (env : RSL.Env) (semantic y1 : Slice U8)
 (domain : RSL.TX1_087.Domain LIB_Instances.VL a obs) (size : semantic.val.length=13831)
 (out : r1_semantic.Verified Unit) (v : verifier.View)
 (native : NNG_FrontValue087.view (NNG_PrepareEmission087.calls env) (NNG_PrepareInput087.input a obs env)
  semantic y1=.ok (.Ok (out,v))) : v.semantic=semantic ∧ v.variant=.S2 := by
 unfold NNG_FrontValue087.view at native
 obtain ⟨reply,called,tail⟩ := NNG_ModelSuccess136.bind_out _ _ _ native
 cases reply with
 | Err e=>cases tail
 | Ok view=>
   have proofSize := NNG_Slices087.proof_length a obs env domain
   have bound : 10055≤(NNG_PrepareInput087.input a obs env).bytes.val.length := by rw [proofSize];decide
   have borrowed := NNG_ViewShape087.borrowed _ semantic y1 bound view called
   have observed := NNG_ReadyView087.observed a obs env view domain (by rw [borrowed.1,size];decide) out v tail
   have same : view=v := observed.1
   subst v
   exact ⟨borrowed.1,variant _ semantic y1 bound view called⟩
#print axioms returned
end AspisR1.NNG_ViewPrefix094
