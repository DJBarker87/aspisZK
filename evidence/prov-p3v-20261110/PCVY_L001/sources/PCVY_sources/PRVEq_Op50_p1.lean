import Aeneas
import NNH_HostCtx
import NOC_Run5bHost
import NNH_LaneModel
import NCV_Reference.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace PCVY_Probe
open AspisR1

theorem op50_slot {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :
    (NOC_HostCtx.sdk c).op50 = NNH_LaneModel.decode := rfl
#print axioms op50_slot

#check @loop.eq_def
#check @Slice.index_usize
#print Slice.index_usize
#check @Slice.index_usize_spec
#print core.slice.index.Slice.index
#print core.slice.index.SliceIndexRangeToUsizeSlice
#print Array.index_usize
#print Array.update
#check @core.num.U64.from_le_bytes
#print core.num.U64.from_le_bytes
#print core.num.U32.from_le_bytes
#print core.result.Result.Insts.CoreOpsTry.branch
#print core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
#print NCV_Reference.Lane
end PCVY_Probe
