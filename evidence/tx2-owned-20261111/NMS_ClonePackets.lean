import NMS_CloneRef241
set_option autoImplicit false
namespace NMS_ClonePackets
open RSL
/-- Full corrected child target. The ONLY difference from RSL is that general
ProgramError clones may stop at their actual getter sites, recursively in234.
The domain, all normal results, Box-bearing values and ordered effects remain
canonical; no snapshot-only restriction is introduced. -/
def RowSpec233 (L : PoolLib) (D : DeployedIds)
 (impl : TX2_233.Args → Env → Obs (Except ProgramError Authenticated)) : Prop :=
 ∀ a env, TX2_233.Domain a → NMS_CloneRef233.Ref L D a env (impl a env)

def RowSpec242 (L : PoolLib) (D : DeployedIds)
 (impl : TX2_242.Args → Env → Obs (Except ProgramError (TX2_242.Validated L))) : Prop :=
 ∀ a env, TX2_242.Domain a → NMS_CloneRef242.Ref L D a env (impl a env)

def RowSpec241 (L : PoolLib) (D : DeployedIds) (V : TX2_241.V2Lib)
 (impl : TX2_241.Args → Env → Obs (Except ProgramError Unit)) : Prop :=
 ∀ a env, TX2_241.Domain V a → NMS_CloneRef241.Ref L D V a env (impl a env)

theorem rejects_const_abort233 (L : PoolLib) (D : DeployedIds) :
 ¬ RowSpec233 L D constAbort := by
 intro packet
 have h := packet ⟨zero32,[],zero32,0,0⟩ env0 trivial
 simp [NMS_CloneRef233.Ref,RS.throw,Spec.pure,constAbort] at h
#print axioms rejects_const_abort233
end NMS_ClonePackets
