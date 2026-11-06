import NLA_DataPrefix
set_option autoImplicit false
noncomputable section
namespace NLA_OwnedData
open Aeneas Aeneas.Std Result
abbrev Account := AdapterRw.r1_pool_adapter.owned.OwnedAccount
abbrev PE := AdapterRw.solana_program_error.ProgramError
/-- A local SDK slot specialization only, never an installed root dictionary.
ProgramError clone is identity. Every other field is irrelevant to data. -/
def cloneOps (ops : AdapterRw.Ops) : AdapterRw.Ops :=
 {ops with op35 := fun e => ok e}

def view (account : Account) : core.result.Result (Slice U8) PE :=
 match account.bytes with
 | .Ok bytes => .Ok bytes.deref
 | .Err e => .Err e

/-- Exact emitted data body, for every vector length and every error variant.
This does not certify the native snapshot or its borrow/cleanup. -/
theorem source (ops : AdapterRw.Ops) (account : Account) :
 AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (cloneOps ops) account =
 ok (view account) := by
 unfold AdapterRw.r1_pool_adapter.owned.OwnedAccount.data view
 cases account.bytes <;> rfl

theorem irrelevant_slots (ops₁ ops₂ : AdapterRw.Ops) (account : Account) :
 AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (cloneOps ops₁) account =
 AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (cloneOps ops₂) account := by
 rw [source,source]

/-- Data selection ignores unrelated account metadata, and retains the SAME
complete vector. The equation is derived from the emitted body. -/
theorem same_bytes (ops : AdapterRw.Ops) (a b : Account)
 (bytes : a.bytes = b.bytes) :
 AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (cloneOps ops) a =
 AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (cloneOps ops) b := by
 rw [source,source]
 unfold view
 rw [bytes]

#print source
#print axioms source
#print axioms irrelevant_slots
#print axioms same_bytes
end NLA_OwnedData
