import NGJ_VERIFIER_IMPORT
import Hiq_DispatchRelease
set_option autoImplicit false
noncomputable section
namespace NGL_EntryRouting
open Aeneas Aeneas.Std Result
open AspisR1
abbrev Key := AdapterRw.solana_pubkey.Pubkey
abbrev R := Result (core.result.Result Unit AdapterRw.solana_program_error.ProgramError)

inductive Call (Account : Type) where
  | first : Key → Slice Account → Slice U8 → Call Account
  | second : Key → Slice Account → Slice U8 → Call Account

structure Reply (State Event : Type) where
  result : R
  state : State
  effects : List Event

structure Children (Account State Event : Type) where
  first : Key → Slice Account → Slice U8 → State → Reply State Event
  second : Key → Slice Account → Slice U8 → State → Reply State Event

def run {Account State Event : Type} (children : Children Account State Event)
    (id : Key) (accounts : Slice Account) (data : Slice U8) (state : State) :
    Reply State Event × List (Call Account) :=
  match Hiq_ReleaseRoute.route data with
  | .first => (children.first id accounts data state, [.first id accounts data])
  | .second => (children.second id accounts data state, [.second id accounts data])
  | .reject => (⟨ok (.Err .InvalidInstructionData),state,[]⟩,[])

/-- The exact source projection of the caller oracle function G. Neither child
    success nor acceptance is assumed; the initial state and original arguments
    are passed to the selected child unchanged. -/
theorem source {Account State Event : Type} (children : Children Account State Event)
    (id : Key) (accounts : Slice Account) (data : Slice U8) (state : State)
    (ops : Hiq_DispatchSource.Ops Account)
    (one : ops.first id accounts data = (children.first id accounts data state).result)
    (two : ops.second id accounts data = (children.second id accounts data state).result) :
    (run children id accounts data state).1.result =
      Hiq_DispatchSource.process_r1_cost_probe_instruction ops id accounts data := by
  rw [Hiq_DispatchRelease.source]
  cases h : Hiq_ReleaseRoute.route data <;> simp only [run,h,one,two]

theorem first_domain (data : Slice U8) (selected : Hiq_ReleaseRoute.route data = .first) :
    data.val = [3#u8,10#u8] ∨ data.val = [3#u8,11#u8] :=
  (Hiq_ReleaseRoute.first_iff data).mp selected

theorem second_domain (data : Slice U8) (selected : Hiq_ReleaseRoute.route data = .second) :
    data.val.take 4 = [65#u8,83#u8,81#u8,56#u8] :=
  ((Hiq_ReleaseRoute.second_iff data).mp selected).2

theorem rejected_frame {Account State Event : Type} (children : Children Account State Event)
    (id : Key) (accounts : Slice Account) (data : Slice U8) (state : State)
    (selected : Hiq_ReleaseRoute.route data = .reject) :
    run children id accounts data state = (⟨ok (.Err .InvalidInstructionData),state,[]⟩,[]) := by
  simp only [run,selected]
#print axioms source
#print axioms first_domain
#print axioms second_domain
#print axioms rejected_frame
end NGL_EntryRouting
