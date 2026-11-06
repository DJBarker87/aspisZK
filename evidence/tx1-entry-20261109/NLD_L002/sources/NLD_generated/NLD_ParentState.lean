import NGL_FirstDecoded
import NJN_GuardModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLD
open Aeneas Aeneas.Std Result
abbrev Public := AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev PE := AdapterRw.solana_program_error.ProgramError
abbrev VE := AdapterRw.aspis_r1_cost_probe.verifier.Error
abbrev Bytes := Slice U8
abbrev Owned := AdapterRw.r1_pool_adapter.owned.OwnedAccount
abbrev Vec := alloc.vec.Vec U8
abbrev Key := AdapterRw.solana_pubkey.Pubkey
abbrev Reply := core.result.Result Vec PE
/-- One explicit carrier shared by all source occurrences. `heap` is the NJN
hand carrier, not yet a certified interpretation of native AccountInfo guards.
Original input bytes are retained separately from later borrowed slices. -/
structure ParentState where
  program : Key
  accounts : Slice Owned
  instruction : Bytes
  originalProof : Bytes
  originalPublic : Bytes
  heap : NJN_GuardModel.Heap
  decoded : Option Public
  proof : Bytes
  publicBytes : Bytes
  split : Usize
  allocations : List Vec
  returned : Option Reply
/-- Occurrence identifiers distinguish repeated uses at identical arguments.
Every event carries the complete before/after state; no payload follows from
pointer identity. Native certificates for these frames are separate obligations. -/
inductive Site where
 | observer | tx1 | errorMap | instructionTen | instructionEleven | accountLength
 | proofIndex | publicIndex | checkpointIndex | distinct | readonlyProof
 | readonlyPublic | checkpointMeta | checkpointData | zero | publicData
 | decoder | validator | common | encoder | proofData | proofStart | proofEnd
 | proofLength | candidateCompare | tag | semantic | proofRange | splitRead
 | firstDecoded | checkpointLength | snapshotProof | snapshotPublic | snapshotCheckpoint
 | ownedChild | mutableBorrow | copy | dropGuard | dropOwned | head | copied
 | dispatch | admission | processChild | returnValue
 deriving DecidableEq
structure Event where
  site : Site
  before : ParentState
  after : ParentState
/-- Full frame equality is a claim about contents and ownership, not an address
comparison. The state itself contains the account, heap and allocations. -/
def Frame (before after : ParentState) : Prop :=
  before.program = after.program ∧ before.accounts = after.accounts ∧
  before.instruction = after.instruction ∧ before.originalProof = after.originalProof ∧
  before.originalPublic = after.originalPublic
end AspisR1.NLD
