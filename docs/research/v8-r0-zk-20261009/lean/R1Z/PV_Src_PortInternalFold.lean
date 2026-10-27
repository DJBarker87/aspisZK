import R1Z.PV_Src_PortInternalMeaning
import R1Z.PV_Src_PortPairsMap
set_option autoImplicit false
namespace R1Z.PV_Src_PortInternalFold
open Aeneas Aeneas.Std R0Z.WriterRefine R0Z.PoseidonRefine
variable {K : Type} [Field K]

theorem model (xs : List (Usize × U32)) (s : Fin 16 → K) :
    PV_Src_PortInternalMeaning.model xs s =
      (xs.map (fun p => liftU p.2)).foldl R0P.poseidonInternalRound s := by
  induction xs generalizing s with
  | nil => rfl
  | cons p xs ih => exact ih _

theorem pairs (xs : List U32) (count : Usize) (s : Fin 16 → K) :
    PV_Src_PortInternalMeaning.model (PV_Src_PortEnumerateTrace.pairs xs count) s =
      (xs.map liftU).foldl R0P.poseidonInternalRound s := by
  rw [model,PV_Src_PortPairsMap.map]

#print axioms model
#print axioms pairs
end R1Z.PV_Src_PortInternalFold
