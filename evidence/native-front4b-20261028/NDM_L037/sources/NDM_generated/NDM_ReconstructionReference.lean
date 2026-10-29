import NDM_GateTotal
import NDM_CommonCarrier
import NDM_StatementReference
set_option autoImplicit false
namespace NDM_ReconstructionReference
open Aeneas Aeneas.Std Result AdapterRw
open aspis_statement.pool_v1
abbrev Request := pair_forest_terminal.PoolV1PairForestTerminalRequestV1
abbrev Auth := r1_pool_adapter.AuthenticatedAsq8Accounts
abbrev Candidate := NDM_CommonCarrier.Candidate
abbrev Statement := NDM_StatementReference.Statement
abbrev Reply := core.result.Result Statement solana_program_error.ProgramError

def asset (request : Request) : U32 := match request.public with
 | .PrivateTransfer p=>p.asset_id
 | .Withdrawal p=>p.asset_id

def statement (request : Request) (a : Auth) (c : Candidate) : Statement :=
 match request.public with
 | .PrivateTransfer p=>.PrivateTransfer (NDM_CommonCarrier.value a c) p
 | .Withdrawal p=>.Withdrawal (NDM_CommonCarrier.value a c) p

def reference (ops : Ops) (request : Request) (a : Auth) (c : Candidate) : Result Reply := do
 let gate ← NDM_GateRef.reconstruction_gate_ref a.live_snapshot.next_pair_index
  c.next_pair_index a.master.identity.asset_id (asset request)
 if gate=1#u8 then ok (.Err .InvalidAccountData)
 else if gate=2#u8 then ok (.Err .InvalidInstructionData)
 else NDM_StatementReference.call ops (statement request a c)

def direct (ops : Ops) (request : Request) (a : Auth) (c : Candidate) : Result Reply :=
 if a.live_snapshot.next_pair_index.val+1=c.next_pair_index.val then
  if a.master.identity.asset_id=asset request then
   NDM_StatementReference.call ops (statement request a c)
  else ok (.Err .InvalidInstructionData)
 else ok (.Err .InvalidAccountData)

/-- Free-slot representability of the reference choice. No installed op52 or
 native Box/validator association is inferred from this theorem. -/
theorem meaning (ops : Ops) (request : Request) (a : Auth) (c : Candidate) :
 reference ops request a c=direct ops request a c := by
 unfold reference NDM_GateRef.reconstruction_gate_ref
 rw [NDM_GateTotal.reference]
 by_cases step : a.live_snapshot.next_pair_index.val+1=c.next_pair_index.val
 · by_cases same : a.master.identity.asset_id=asset request
   · simp [step,same,direct]
   · simp [step,same,direct]
 · simp [step,direct]

def install (base : Ops) : Ops := {base with op52:=reference base}

theorem selected (base : Ops) (r : Request) (a : Auth) (c : Candidate) :
 (install base).op52 r a c=direct base r a c := meaning base r a c

theorem digest_error_preserved (base : Ops) :
 (install base).op43=base.op43 ∧ (install base).op44=base.op44 := ⟨rfl,rfl⟩

theorem decoders_preserved (base : Ops) :
 (install base).op50=base.op50 ∧ (install base).op51=base.op51 := ⟨rfl,rfl⟩

#print axioms meaning
#print axioms selected
#print axioms digest_error_preserved
#print axioms decoders_preserved
end NDM_ReconstructionReference
