import NNG_Input094
import NNG_ConcreteCalls094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_InputTransport094
open Aeneas Aeneas.Std Result NMT_tx1 NNG_Carriers094

theorem bytes (b : RSL.Bytes) : NNG_Data137.bytes b=LIBC_Bytes.raw b := by
 unfold NNG_Data137.bytes LIBC_Bytes.raw
 split <;> rfl
#print axioms bytes

theorem zero : Array.repeat 29#usize (fromT3 AspisR1PublicPreparation.aspis_core.field.WideExact.ZERO)=
 arr fromT3 LIB_Instances.VL.zeroE29 := by
 have mapped := congrArg (arr fromT3) NNG_ConcreteCalls094.zero_array
 exact (arr_inverse toT3 fromT3 toT3_inverse _).symm.trans mapped
#print axioms zero
end AspisR1.NNG_InputTransport094
