import FJa_PoseidonLowOnRun
import FJh_Base
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJh_LowModels
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (decoded)
open FJh_Base (State)
theorem cell (s : State) (i : Nat) (hi : i<16) :
    FIv_NativeArray.value s i=decoded s ⟨i,hi⟩ := by
  simp only [FIv_NativeArray.value,List.getElem?_eq_getElem (by rw [s.property];exact hi)]
  rfl
theorem internal (s : FJa_PoseidonOrigins.Selectors) :
    FJa_LocalWeightFold.model s [2#usize,3#usize,4#usize,5#usize,6#usize,7#usize,8#usize] 0=
    (List.ofFn (fun i : Fin 7=>decoded s.local ⟨i.val+2,by change i.val+2<16;omega⟩)).foldl (·+·) 0 := by
  have terms : ([2#usize,3#usize,4#usize,5#usize,6#usize,7#usize,8#usize].map
      (fun i=>FIv_NativeArray.value s.local i.val))=
      List.ofFn (fun i : Fin 7=>decoded s.local ⟨i.val+2,by change i.val+2<16;omega⟩) := by
    simp only [List.map_cons,List.map_nil]
    rw [cell s.local 2 (by decide),cell s.local 3 (by decide),cell s.local 4 (by decide),
      cell s.local 5 (by decide),cell s.local 6 (by decide),cell s.local 7 (by decide),cell s.local 8 (by decide)]
    rfl
  exact congrArg (fun xs=>xs.foldl (·+·) 0) terms
#print axioms cell
#print axioms internal
end AspisR1.FJh_LowModels
end
