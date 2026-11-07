import NMV_FullState
set_option autoImplicit false
namespace NMV_WeakFold
open RSL

/-- G1b's free weak specialization of the SAME parametric 240 fold. There
is no Root0 hypothesis: the only child parameter is the full weak 241 law. -/
theorem fold240 (L : PoolLib) (D : DeployedIds) (V : TX2_241.V2Lib)
 (w : Bytes → Bytes → Bytes → Spec (Except V.VErr Unit))
 (child : TX2_241.Args → Env → Obs (Except ProgramError Unit))
 (packet : TX2_241.RowSpec_241 L D (TCK.weaken V w) child)
 (a : TX2_240.Args) (s : SdkState) (env : Env)
 (o : Obs (Except ProgramError Unit × SdkState))
 (h : NMV_RslFold.stage2 child a s env o) :
 TX2_240.Ref L D (TCK.weaken V w) a s env o :=
 NMV_RslFold.fold240 L D (TCK.weaken V w) child packet a s env
   (TCK.domain240_weaken V w a s) o h

#print axioms fold240
end NMV_WeakFold
