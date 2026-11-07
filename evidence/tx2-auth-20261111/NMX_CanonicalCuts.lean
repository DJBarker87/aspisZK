import NMX_CanonicalTarget
set_option autoImplicit false
namespace NMX_CanonicalCuts
open RSL
/-- The original selected-lane bytes are the SAME argument on both sides;
no 768-byte or successful-decode premise is introduced. -/
theorem lane (native : Bytes → Env → Obs (Except ProgramError LaneState))
 (child : NMX_CanonicalTarget.RowSpec_217 native) (bytes : Bytes) (env : Env) :
 Spec.call TX2_217.Domain TX2_217.Ref bytes env (native bytes env) :=
 ⟨True.intro,child bytes env True.intro⟩

/-- Registry call at the complete original seven-argument tuple. -/
theorem registry (L : PoolLib) (D : DeployedIds)
 (native : TX2_234.Args → Env → Obs (Except ProgramError Unit))
 (child : NMX_CanonicalTarget.RowSpec_234 L D native)
 (verifier pool : B32) (masterAccount : OwnedAccount) (master : Master)
 (registry entry : OwnedAccount) (slot : UInt64) (env : Env) :
 let args : TX2_234.Args := ⟨verifier,pool,masterAccount,master,registry,entry,slot⟩
 Spec.call TX2_234.Domain (TX2_234.Ref L D) args env (native args env) :=
 ⟨True.intro,child _ env True.intro⟩
#print axioms lane
#print axioms registry
end NMX_CanonicalCuts
