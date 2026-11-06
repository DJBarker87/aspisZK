import NJU_FinishInput
import NJU_WeakPairInstantiation
set_option autoImplicit false
namespace AspisR1.NJU_WeakPairCaller
open Aeneas Aeneas.Std Result AspisR1Stage2 LPi_FieldValues NIT_Cuts
abbrev E := AspisR1Stage2.aspis_core.field.wide_exact.WideExact
theorem alphas (proof:Slice U8) (v:verifier.View) (p:verifier.Prepared)
 (a:verifier.Accumulator) (h:NJU_FinishInput.Holds proof v p a):
 ∀ x∈(FIo_Install.toSlice p.alpha.to_slice).val,canonE x:=by
 intro x hx
 obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hx
 obtain ⟨i,hi,eq⟩:=List.mem_iff_getElem.mp hy
 change i<p.alpha.val.length at hi
 apply NIG_FinishAlpha.canonical
 apply h.alpha i (by rw [p.alpha.property] at hi;exact hi)
 exact (List.getElem?_eq_getElem hi).trans (congrArg some eq)

theorem new_owner (r:NP6_StdModel.Reservation) (proof:Slice U8)
 (v:verifier.View) (p:verifier.Prepared) (a:verifier.Accumulator)
 (h:NJU_FinishInput.Holds proof v p a) (w:FIo_Install.W)
 (run:(NIG_Slots.installed r).op3 p.variant p.semantic_alpha p.z=ok (.Ok w)):
 (FIo_Install.toWeights w).variant=FIo_Native.transport.Variant.S2 ∧
 NHI_TensorOuterStep.Factors (FIo_Install.toWeights w) ∧
 NHI_CellCanon.array (FIo_Install.toWeights w).extra:=by
 rw [NIG_Slots.NHM_new,h.s2] at run
 exact NIG_NewReply.returned p.semantic_alpha p.z h.semantic h.points w run

theorem caller (r : NP6_StdModel.Reservation) (proof : Slice U8) (v : verifier.View)
 (p : verifier.Prepared) (a : verifier.Accumulator) (input : NJU_FinishInput.Holds proof v p a)
 (w : FIo_Install.W) (new : (NIG_Slots.installed r).op3 p.variant p.semantic_alpha p.z=ok (.Ok w)) :
 NJU_WeakPairDomain.Domain (FIo_Install.toWeights w) (NIT_PairDomain.alpha p)
 v.final_message (FIo_Install.toE p.kappa) := by
 obtain ⟨s2,factors,extra⟩:=new_owner r proof v p a input w new
 have canon:=alphas proof v p a input
 change LPi_FieldValues.canonical (NIT_PairDomain.alpha p) at canon
 exact ⟨s2,factors,extra,canon,input.final_size,NIG_FinishAlpha.canonical _ input.kappa⟩

#print axioms alphas
#print axioms new_owner
#print axioms caller
end AspisR1.NJU_WeakPairCaller
