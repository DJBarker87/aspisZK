import R1Z.PV_Src_PortTables
import R0Z.PoseidonConstLift
set_option autoImplicit false
namespace R1Z.PV_Src_PortFinalList
open Aeneas Aeneas.Std R0Z.WriterRefine R0Z.PoseidonRefine
variable {K : Type} [Field K]

theorem source : (BuilderForestAdmissionPort.poseidon2.EXTERNAL_FINAL.val.map (liftA (K := K))) =
    List.ofFn (fun i : Fin 4 => R0P.poseidonExternalFinal (K := K) i) := by
  rw [PV_Src_PortTables.final_constants]
  apply List.ext_getElem
  · simp only [List.length_map,R0PoseidonCopy.EXTERNAL_FINAL.property,List.length_ofFn,UScalar.ofNatCore_val_eq]
  · intro i hi hj
    rw [List.getElem_map,List.getElem_ofFn]
    have hix : i < R0PoseidonCopy.EXTERNAL_FINAL.val.length := by simpa only [List.length_map] using hi
    funext lane
    change liftU (K := K) ((R0PoseidonCopy.EXTERNAL_FINAL.val[i]).val[lane.val]!) = _
    have h := ef_rows (K := K) ⟨i,by simpa only [List.length_ofFn] using hj⟩ lane
    simpa only [getElem!_pos R0PoseidonCopy.EXTERNAL_FINAL.val i (by simpa only [List.length_map] using hi)] using h

#print axioms source
end R1Z.PV_Src_PortFinalList
