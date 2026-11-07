import NMX_Emitted
import NGL_CloneDomain
set_option autoImplicit false
noncomputable section
namespace NMX_ErrorCloneCut
open Aeneas Aeneas.Std Result AdapterRw
/-- Exact actual getter arm on an arbitrary deferred ProgramError. The clone
is a reached opaque operation; an allocation failure here precedes the master
Box allocation. This is a source equation, not a reachable-runtime witness. -/
theorem data_error (ops : Ops) (a : r1_pool_adapter.owned.OwnedAccount)
 (e : solana_program_error.ProgramError) (bytes : a.bytes = .Err e) :
 r1_pool_adapter.owned.OwnedAccount.data ops a =
 (do let cloned ← ops.op35 e; ok (.Err cloned)) := by
 simp only [r1_pool_adapter.owned.OwnedAccount.data,bytes]

theorem data_stop (ops : Ops) (a : r1_pool_adapter.owned.OwnedAccount)
 (e : solana_program_error.ProgramError) (bytes : a.bytes = .Err e)
 (failure : Aeneas.Std.Error) (clone : ops.op35 e = .fail failure) :
 r1_pool_adapter.owned.OwnedAccount.data ops a = .fail failure := by
 rw [data_error ops a e bytes,clone]
 rfl
#print axioms data_error
#print axioms data_stop
end NMX_ErrorCloneCut
end
