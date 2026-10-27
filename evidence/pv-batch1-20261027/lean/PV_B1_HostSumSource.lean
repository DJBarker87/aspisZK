import PV_B1_Install
import PV_B1_HostSumValue
set_option autoImplicit false
noncomputable section
namespace PV_B1_HostSumSource
open Aeneas Aeneas.Std Result PV_B1_Carrier230 PV_B1_HostSumValue

def original_row (xs : Slice HQ) : Option HQ :=
  if Slice.len xs=1024#usize then some (xs.val.foldl add zero) else none

theorem original_transport (xs : Slice HQ) :
    Option.map fromQ (PV_B1_SumOriginal.original_row (PV_B1_Transport.sliceMap toQ xs))=original_row xs := by
  unfold PV_B1_SumOriginal.original_row original_row
  rw [PV_B1_Transport.slice_length]
  by_cases h : Slice.len xs=1024#usize
  · simp only [h,if_true,Option.map_some,PV_B1_Transport.sliceMap]
    rw [←to_zero]
    exact congrArg some (fold xs.val zero)
  · simp only [h,if_false,Option.map_none]

theorem op230_source [PV_B1_Host.ExternalTypes] (ops : PV_B1_Host.ExternalFuns) (xs : Slice HQ) :
    (PV_B1_Install.selected ops).op230 xs=ok (original_row xs) := by
  rw [PV_B1_Install.op230_source,original_transport]
#print axioms original_transport
#print axioms op230_source
end PV_B1_HostSumSource
