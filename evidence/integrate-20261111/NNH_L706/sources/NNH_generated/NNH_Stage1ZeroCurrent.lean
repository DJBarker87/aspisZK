import NNH_MappedOk
import NND_ScalarLaws
import NND_CarrierInjective
import NMT_345ZeroSource
set_option autoImplicit false
namespace NNH_Stage1ZeroCurrent
open Aeneas Aeneas.Std AdapterRw NND_Carrier NNH_ModelCarrier
/-- Rev3-compatible carrier proof. It deliberately avoids the obsolete
NND_AccountCarrier object, which duplicates an RSL-owned equation theorem. -/
theorem projection (data : Slice U8) :
 outer (reply id) (r1_pool_adapter.owned.require_zero data)=.ok (RSL.requireZero (bytes data)) := by
 have all_zero : (bytes data).all (· == 0)=data.val.all (· == 0#u8) := by
  simp only [bytes,List.all_map,Function.comp_def]
  apply congrArg (fun f : U8 → Bool => data.val.all f)
  funext x
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  rw [←byte_zero]
  exact byte_eq_iff x 0#u8
 rw [NMT_345.zero_source]
 unfold RSL.requireZero
 rw [all_zero]
 cases data.val.all (· == 0#u8) <;> rfl

theorem source (data : Slice U8) (zero : RSL.requireZero (bytes data)=.ok ()) :
 r1_pool_adapter.owned.require_zero data=.ok (.Ok ()) := by
 have mapped:=projection data
 rw [zero] at mapped
 obtain ⟨unit,native,same⟩ := NNH_MappedOk.value _ _ _ mapped
 cases unit
 exact native
#print axioms projection
#print axioms source
end NNH_Stage1ZeroCurrent
