import NMX_CanonicalTarget
set_option autoImplicit false
namespace NMX_CanonicalErrorPrefix
open RSL
/-- Canonical master-data error arm, before its decoder/Box allocation.
This exposes the silent-projection assumption without asserting native clone
termination or any successful decoder/child outcome. -/
theorem master_data (L : PoolLib) (D : DeployedIds) (a : TX2_233.Args)
 (p m c l r e v : OwnedAccount) (failure : ProgramError)
 (proof : readonlyBuffer p = .ok ())
 (verifier : verifierCheckpoint v a.verifier_program false = .ok ())
 (master : readonlyAccount m a.pool_program = .ok ())
 (checkpoint : readonlyAccount c a.pool_program = .ok ())
 (lane : readonlyAccount l a.pool_program = .ok ())
 (distinct : requireDistinct [p,m,c,l,r,e,v] = .ok ())
 (data : m.bytes = .error failure) :
 TX2_233.body L D a p m c l r e v = RS.throw failure := by
 simp only [TX2_233.body,proof,verifier,master,checkpoint,lane,distinct,
  RS.ofExcept_ok,RS.seq_pure,OwnedAccount.data,data,RS.ofExcept_error,RS.bind_throw]

/-- Thus the canonical body admits no allocation abort on this entered error
arm. Whether native String.clone can stop here is a separate std-interpretation
obligation, not resolved by this theorem or by a chosen op35 reply. -/
theorem master_no_abort (L : PoolLib) (D : DeployedIds) (a : TX2_233.Args)
 (p m c l r e v : OwnedAccount) (failure : ProgramError)
 (proof : readonlyBuffer p = .ok ())
 (verifier : verifierCheckpoint v a.verifier_program false = .ok ())
 (master : readonlyAccount m a.pool_program = .ok ())
 (checkpoint : readonlyAccount c a.pool_program = .ok ())
 (lane : readonlyAccount l a.pool_program = .ok ())
 (distinct : requireDistinct [p,m,c,l,r,e,v] = .ok ())
 (data : m.bytes = .error failure) (env : Env) (events : List Event) :
 ¬ TX2_233.body L D a p m c l r e v env ⟨.abort,events⟩ := by
 rw [master_data L D a p m c l r e v failure proof verifier master checkpoint lane distinct data]
 intro impossible
 have h := congrArg Obs.exit impossible
 cases h
#print axioms master_data
#print axioms master_no_abort
end NMX_CanonicalErrorPrefix
