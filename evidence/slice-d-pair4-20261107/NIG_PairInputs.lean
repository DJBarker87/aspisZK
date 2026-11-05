import NIG_FinishExport
import NIG_NewReply
set_option autoImplicit false
namespace NIG_PairInputs
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 LPi_FieldValues
abbrev E:=aspis_core.field.wide_exact.WideExact

theorem alpha_prefix (p:verifier.Prepared):
 core.array.Array.index (core.ops.index.IndexSlice
  (core.slice.index.SliceIndexRangeToUsizeSlice E)) p.alpha {«end»:=2#usize}=ok p.alpha.to_slice:=by
 change (if (2:Nat)≤p.alpha.val.length then ok (⟨List.slice 0 2 p.alpha.val,_⟩:Slice E) else fail .panic)=_
 have len:p.alpha.val.length=2:=p.alpha.property
 simp only [len,le_refl,ite_true]
 congr 1
 apply Subtype.ext
 simp [List.slice,len]

theorem alphas (proof:Slice U8) (v:verifier.View) (p:verifier.Prepared)
 (a:verifier.Accumulator) (h:NIG_FinishInput.Domain proof v p a):
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
 (h:NIG_FinishInput.Domain proof v p a) (w:FIo_Install.W)
 (run:(NIG_Slots.installed r).op3 p.variant p.semantic_alpha p.z=ok (.Ok w)):
 (FIo_Install.toWeights w).variant=FIo_Native.transport.Variant.S2 ∧
 NHI_TensorOuterStep.Factors (FIo_Install.toWeights w) ∧
 NHI_CellCanon.array (FIo_Install.toWeights w).extra:=by
 rw [NIG_Slots.NHM_new,h.s2] at run
 exact NIG_NewReply.returned p.semantic_alpha p.z h.semantic h.points w run

theorem final_width (proof:Slice U8) (v:verifier.View) (p:verifier.Prepared)
 (a:verifier.Accumulator) (h:NIG_FinishInput.Domain proof v p a):v.final_message.val.length=2048:=by
 exact h.final_words.1
#print axioms alpha_prefix
#print axioms alphas
#print axioms new_owner
#print axioms final_width
end NIG_PairInputs
