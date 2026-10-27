import R1Z.PV_Src_PortTables
import R0Z.PoseidonConstLift
set_option autoImplicit false
namespace R1Z.PV_Src_PortInternalList
open Aeneas Aeneas.Std R0Z.WriterRefine R0Z.PoseidonRefine
variable {K : Type} [Field K]

theorem source : (BuilderForestAdmissionPort.poseidon2.INTERNAL.val.map (liftU (K := K))) =
    List.ofFn (fun i : Fin 14 => R0P.poseidonInternalConstants (K := K) i) := by
  rw [PV_Src_PortTables.internal]
  apply List.ext_getElem
  · simp only [List.length_map,R0PoseidonCopy.INTERNAL.property,List.length_ofFn,UScalar.ofNatCore_val_eq]
  · intro i hi hj
    rw [List.getElem_map,List.getElem_ofFn]
    have h := ic_all (K := K) ⟨i,by simpa only [List.length_ofFn] using hj⟩
    simpa only [getElem!_pos R0PoseidonCopy.INTERNAL.val i (by simpa only [List.length_map] using hi)] using h

#print axioms source
end R1Z.PV_Src_PortInternalList
