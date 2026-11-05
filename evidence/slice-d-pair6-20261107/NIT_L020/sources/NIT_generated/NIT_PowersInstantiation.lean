import NIT_FinalCompleteness
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIT_PowersInstantiation
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairComposition

/-- The SAME decoded two alphas instantiate the CLOSED powers4 packet and the
Initial native cut. No independently chosen successful powers result. -/
theorem initial (alpha : Array E 2#usize) (ca : canonical alpha) :
 ∃ (ap0 ap1 : Powers) (l : Initial) (parts : Parts),
 cutInitial alpha l ap0 ap1 parts ∧
 FIo_Native.weights.powers 4#usize (epick alpha 0)=ok ap0 ∧
 FIo_Native.weights.powers 4#usize (epick alpha 1)=ok ap1 ∧
 canonical ap0 ∧ canonical ap1 := by
 obtain ⟨ap0,source0,model0,c0⟩ := NFW_PowersCohort.source 4#usize (epick alpha 0)
  (epick_canonical alpha ca 0)
 obtain ⟨ap1,source1,model1,c1⟩ := NFW_PowersCohort.source 4#usize (epick alpha 1)
  (epick_canonical alpha ca 1)
 let l : Initial := ⟨alpha,(fun side=>if side=0 then ap0 else ap1),2⟩
 let parts : Parts := Array.repeat 7#usize NHI_Scalar.zero
 refine ⟨ap0,ap1,l,parts,?_,source0,source1,c0,c1⟩
 refine ⟨ca,?_,rfl,rfl,?_,?_,?_⟩
 · intro side
   fin_cases side
   · exact c0
   · exact c1
 · rfl
 · rfl
 · intro slot small
   simp [parts,epick,Array.repeat,List.getElem?_replicate]

/-- The actual original kappa supplies powers7, whose canonicality supplies every
Final-loop multiplication domain. Both powers and fold use the SAME array. -/
theorem powers7_final (kappa : E) (ck : canonE kappa) (parts : Parts)
 (cp : canonical parts) :
 ∃ powers out,FIo_Native.weights.powers 7#usize kappa=ok powers ∧
 canonical powers ∧
 FinalTrace parts powers 8 ({start:=0#usize,«end»:=7#usize},NHI_Scalar.zero) out ∧
 FIo_Native.weights.Weights.pair_loop17 {start:=0#usize,«end»:=7#usize}
  parts powers NHI_Scalar.zero=ok out ∧ canonE out := by
 obtain ⟨powers,source,model,canonical⟩ := NFW_PowersCohort.source 7#usize kappa ck
 obtain ⟨out,trace,loop,co⟩ := NIT_FinalCompleteness.complete parts powers cp canonical
 exact ⟨powers,out,source,canonical,trace,loop,co⟩

#print axioms initial
#print axioms powers7_final
end AspisR1.NIT_PowersInstantiation
