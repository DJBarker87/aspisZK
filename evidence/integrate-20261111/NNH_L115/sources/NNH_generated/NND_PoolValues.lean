import NND_PoolReturned
set_option autoImplicit false
namespace NND_PoolValues
open RSL NND_Returned
/-- Intermediate value-transport obligations for CLOSED Pool children. This is
not a RowSpec and is never an admitted root hypothesis. Each field must be
proved for the concrete CLOSED carrier installation. -/
structure Values (L : PoolLib) where
 scan : Bytes → Env → Except ProgramError (L.Afterstate × Nat)
 reconstruct : L.Request → Authenticated → L.Afterstate → Env → Except ProgramError L.Statement
 encode : L.Statement → Env → Option Bytes
 emit : L.Statement → Env → Except ProgramError Unit
 scan_ret : ∀ b env, Returns (L.scanProof b) env (scan b env)
 reconstruct_ret : ∀ q a s env, Returns (L.reconstruct q a s) env (reconstruct q a s env)
 encode_ret : ∀ s env, Returns (L.encodeStatement s) env (encode s env)
 emit_ret : ∀ s env, Returns (L.emitResult s) env (emit s env)
end NND_PoolValues
