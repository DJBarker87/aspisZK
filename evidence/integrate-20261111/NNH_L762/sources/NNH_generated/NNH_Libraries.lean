import LIB_Instances
import LIBB_V2Star
import LIBB_PoolLib
import NNH_Stage2Eval
set_option autoImplicit false
noncomputable section
namespace NNH_Libraries
open RSL
abbrev L := LIBB_PoolLib.library
abbrev D := LIB_Instances.D
abbrev V0 := LIBB_V2Star.library
abbrev VL := LIB_Instances.VL
abbrev P := LIB_Instances.P
abbrev C := LIB_Instances.C
/-- Concrete library Returns, at the unchanged canonical V0. -/
def authValues : NNH_Tx2Values.Values V0 where
 auth := LIBB_V2Star.values.auth
 auth_ret := LIBB_V2Star.values.auth_ret
abbrev tx2Value := NNH_Stage2Eval.value L D V0 LIBB_PoolLib.values authValues

theorem tx2_returns (a : TX2_241.Args) (env : Env) :
 NND_Returned.Returns (TX2_241.Ref L D V0 a) env (tx2Value a env) :=
 NNH_Stage2Eval.returned L D V0 LIBB_PoolLib.values authValues a env

#print axioms tx2_returns
end NNH_Libraries
