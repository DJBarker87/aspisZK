import NIS_OwnedHeaders
import NIS_Distinct3
set_option autoImplicit false
namespace NIV_OwnedPrefixes
open Aeneas Aeneas.Std Result AdapterRw
abbrev Account := r1_pool_adapter.owned.OwnedAccount
abbrev PE := solana_program_error.ProgramError

def accounts3 (a b c : Account) : Slice Account :=
  ⟨[a,b,c],by simp only [List.length_cons,List.length_nil]; scalar_tac⟩

/-- Exact native guard assertion and forbidden-decoder suffix. This definition
contains no acceptance or endpoint equation; e is the selected full error.
Native harness/domain associations remain in NIV_CERTIFICATES.md. -/
def rejectionCut {Output : Type} (reply : core.result.Result Output PE)
    (e : PE) (decoderReached : Bool) : Prop := reply = .Err e ∧ decoderReached = false

/-- Full-record staged guard association. The header comparison and distinct
reply are named child observations, to be instantiated from CLOSED laws on
these SAME arguments, never from parent success. -/
theorem distinct_error (ops : AdapterRw.Ops) (program : solana_pubkey.Pubkey)
    (a b c : Account) (data : Slice U8) (e : PE)
    (ten : ops.op1 core.cmp.PartialEqU8 data
      (Array.make 2#usize [3#u8,10#u8]) = ok true)
    (distinct : r1_pool_adapter.owned.require_distinct_accounts ops
      (Array.make 3#usize [a,b,c]) = ok (.Err e)) :
    r1_pool_adapter.owned.stage1_owned ops program (accounts3 a b c) data = ok (.Err e) := by
  simp [r1_pool_adapter.owned.stage1_owned,ten,accounts3,distinct]

/-- Later native fields and arbitrary Vec/error payloads are not restricted
by this source prefix law. It supplies no skipped decoder or allocator law. -/
theorem proof_readonly_error (ops : AdapterRw.Ops) (program : solana_pubkey.Pubkey)
    (a b c : Account) (data : Slice U8) (e : PE)
    (ten : ops.op1 core.cmp.PartialEqU8 data
      (Array.make 2#usize [3#u8,10#u8]) = ok true)
    (distinct : r1_pool_adapter.owned.require_distinct_accounts ops
      (Array.make 3#usize [a,b,c]) = ok (.Ok ()))
    (readonly : r1_pool_adapter.owned.require_readonly_buffer a = ok (.Err e)) :
    r1_pool_adapter.owned.stage1_owned ops program (accounts3 a b c) data = ok (.Err e) := by
  simp [r1_pool_adapter.owned.stage1_owned,ten,accounts3,distinct,readonly]

#print axioms distinct_error
#print axioms proof_readonly_error
end NIV_OwnedPrefixes
