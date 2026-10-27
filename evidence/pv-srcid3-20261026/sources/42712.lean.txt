import R1Z.PV_Src_PortFullMeaning
import R1Z.PV_Src_PortPairsMap
set_option autoImplicit false
namespace R1Z.PV_Src_PortFullFold
open Aeneas Aeneas.Std R0Z.WriterRefine R0Z.PoseidonRefine
open PV_Src_PortSboxStep
variable {K : Type} [Field K]

theorem model (xs : List (Usize × State)) (s : Fin 16 → K) :
    PV_Src_PortFullMeaning.model xs s =
      (xs.map (fun p => liftA p.2)).foldl R0P.poseidonFullRound s := by
  induction xs generalizing s with
  | nil => rfl
  | cons p xs ih => exact ih _

theorem pairs (xs : List State) (count : Usize) (s : Fin 16 → K) :
    PV_Src_PortFullMeaning.model (PV_Src_PortEnumerateTrace.pairs xs count) s =
      (xs.map liftA).foldl R0P.poseidonFullRound s := by
  rw [model,PV_Src_PortPairsMap.map]

#print axioms model
#print axioms pairs
end R1Z.PV_Src_PortFullFold
