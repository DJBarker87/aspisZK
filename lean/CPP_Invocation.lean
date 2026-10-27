import Hir_Call
import CPP_Second
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_Invocation
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call
attribute [local instance] Classical.propDecidable

/-- Unlike Layout, a native invocation retains the original account count.
The release wrapper checks this before snapshot allocation. -/
structure Invocation (A : Type) where
  call : Call A
  count : Nat

abbrev PE := AdapterRw.solana_program_error.ProgramError
abbrev FirstResult (A : Type) := Result (core.result.Result
  (alloc.vec.Vec U8 × Heap (Nat → Record) × A) PE)
abbrev SecondResult (A : Type) := Result (core.result.Result (Heap (Nat → Record) × A) PE)

def first {A : Type} (native : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (store : Store)
    (input : Invocation A) : FirstResult A :=
  if Hiq_ReleaseRoute.stage1 input.call.data ∧ input.count = 3 then
    S2W_D189Wrappers.first native copy allocator (load store input.call.layout) id input.call.data input.call.state
  else ok (.Err .InvalidInstructionData)

def second {A : Type} (native : S2W_ExtractionBoundary.Second)
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (store : Store)
    (input : Invocation A) : SecondResult A :=
  if Hiq_ReleaseRoute.asq8 input.call.data ∧ input.count = 7 then
    S2W_D189Wrappers.second native allocator (load store input.call.layout) id input.call.data input.call.slot input.call.state
  else ok (.Err .InvalidInstructionData)

/-- Computed ledger projection, with the exact native reply retained.
No malformed account count is silently expanded to three/seven snapshots. -/
def native {A : Type} (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (store : Store)
    (input : Invocation A) : Effect A :=
  match Hiq_ReleaseRoute.route input.call.data with
  | .first => firstEffect store input.call (first native1 copy allocator id store input)
  | .second => (store,.rollback,.inr (second native2 allocator id store input))
  | .reject => (store,.rollback,.inr (.ok (.Err .InvalidInstructionData)))
end AspisR1.CPP_Invocation
end
