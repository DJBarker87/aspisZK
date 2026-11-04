import Lean
import NGF_NEX_ReadDomains
import NFY_Part030

set_option autoImplicit false
noncomputable section
namespace NGF_NEX_DigestCallDomains
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

def afterArgument (bytes : Array U8 688#usize) (n : Fin 21) : Array U8 32#usize :=
  ⟨(bytes.val.drop (16+32*n.val)).take 32,(NGF_NEX_ReadDomains.after_window bytes n.val n.isLt).1⟩

def snapshotArgument (bytes : Array U8 800#usize) (n : Fin 21) : Array U8 32#usize :=
  ⟨(bytes.val.drop (128+32*n.val)).take 32,(NGF_NEX_ReadDomains.snapshot_window bytes n.val n.isLt).1⟩

/-- The closed digest model law is instantiated at each SAME logged 32-byte
argument. No DigestDecode hypothesis remains at these internal call sites. -/
theorem after_digest (bytes : Array U8 688#usize) (n : Fin 21) :
    atomic_statement.decode_digest_canonical (afterArgument bytes n) =
    ok (NFY_NBP_DigestDecode.decoded (afterArgument bytes n)) := NFY_NBP_DigestDecode.result _

theorem snapshot_digest (bytes : Array U8 800#usize) (n : Fin 21) :
    atomic_statement.decode_digest_canonical (snapshotArgument bytes n) =
    ok (NFY_NBP_DigestDecode.decoded (snapshotArgument bytes n)) := NFY_NBP_DigestDecode.result _

theorem exact_after (bytes : Array U8 688#usize) (n : Fin 21) :
    pool_v1.pair_terminal.exact 32#usize (afterArgument bytes n).to_slice =
    ok (.Ok (afterArgument bytes n)) := by
  rw [NBH_Exact.source]
  unfold NBH_Exact.result
  split
  · rfl
  · rename_i bad
    exact False.elim (bad (afterArgument bytes n).property)

#print axioms after_digest
#print axioms snapshot_digest
#print axioms exact_after
end NGF_NEX_DigestCallDomains

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
