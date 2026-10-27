import RPv_FJk_OpeningSelected
import RPv_FJk_CopyRowTransport
import RPv_FIw_PublicModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_ClaimsModel
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (K)
open FIw_ArrayValue (decoded)
def claims (a : Array field.QM31 84#usize) : Fin 3 → Fin 29 → K :=
  fun j l=>FIv_NativeArray.value a (j.val*28+l.val)
def openings (a : Array field.QM31 84#usize) : R0P.Openings K :=
  ⟨fun i=>claims a 0 (Fin.castLE (by omega) i),
   fun i=>claims a 1 (Fin.castLE (by omega) i),
   fun i=>claims a 2 (Fin.castLE (by omega) i)⟩
/-- The three actual width28 gathers have exactly the model opening cells. -/
theorem value (a : Array field.QM31 84#usize) (z s x : Array field.QM31 16#usize)
    (hz : array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
      pool_v1.pair_forest_semantic_terminal.composition_parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO a=ok z)
    (hs : array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
      pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO a=ok s)
    (hx : array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
      pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO a=ok x) :
    FIw_PublicModel.openings ⟨z,s,x⟩=openings a := by
  have vz:=FJk_OpeningSelected.z a z hz
  have vs:=FJk_OpeningSelected.succ a s hs
  have vx:=FJk_OpeningSelected.xor12 a x hx
  have cells (b : Array field.QM31 16#usize) :
      (fun i : Fin 16=>FIv_NativeArray.value b i.val)=decoded b := funext (fun i=>(FJk_CopyRowTransport.cell b i))
  unfold FIw_PublicModel.openings
  rw [cells z,cells s,cells x,vz,vs,vx]
  simp only [openings,claims]
  congr 1 <;> funext i <;> congr 1 <;> change _=_*28+i.val <;> omega
#print axioms value
end AspisR1.FJn_ClaimsModel
end
