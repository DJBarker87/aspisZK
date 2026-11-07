import NNE_AcceptanceSig
import NNE_BankImage
set_option autoImplicit false
noncomputable section
namespace NNE_Observed
open Aeneas Aeneas.Std AspisR1 S2W_D189Entry S2W_ReturnedCheckpoint
open Hist_Store Hist_RuntimeEntry CPP_BankState
open RSL
abbrev Observation := Obs (Except ProgramError Unit × SdkState)

/-- The physical trace chooses the Bool state from the actual exit. -/
def completed (o : Observation) : Bool := match o.exit with
 | .ret _ => true
 | .abort | .diverge => false

def entry (bank : Bank) (input : CPP_Invocation.Invocation Bool) : Entry :=
 load bank.cells (CPP_BankState.invocation bank input).call.layout

def args (bank : Bank) (input : CPP_Invocation.Invocation Bool)
 (p : S2W_ExtractionBoundary.Program) : TX2_213.Args :=
 NNE_EntryArgs.args (entry bank input) input.count p input.call.data

def state (bank : Bank) (input : CPP_Invocation.Invocation Bool) : SdkState :=
 NNE_Entry.state (entry bank input) 0

/-- Physical data/balance/event representation only. The input Bool is the
actual invocation's abort bit. No model, native result, wrapper acceptance or
CPG Step appears here. Runtime rollback is retained on unsuccessful exits. -/
def Assoc (before after : Bank) (input : CPP_Invocation.Invocation Bool)
 (o : Observation) (event : S2X.AccountEvent) : Prop :=
 input.call.state = completed o ∧
 match o.exit with
 | .ret (.ok (),post) =>
   NNE_BankImage.Image post after ∧ NNE_BankImage.Metadata before after ∧
   NNE_BankImage.Events o.events event ∧
   (Hiq_ReleaseRoute.stage1 input.call.data → input.count = 3 →
     ∃ saved, NNE_PhysicalAccepted.Out1 saved o)
 | .ret (.error _,_) | .abort | .diverge => after = before ∧ event = .rollback

/-- Selected Ok occurrences have true states by definition, rather than an
allocator-success premise supplied by a row or trust item. -/
theorem selected_true (o : Observation) (post : SdkState)
 (h : o.exit = .ret (.ok (),post)) : completed o = true := by rw [completed,h]

theorem state_iff (before after : Bank) (input : CPP_Invocation.Invocation Bool)
 (o : Observation) (event : S2X.AccountEvent) (rep : Assoc before after input o event) :
 input.call.state = true ↔ ∃ r s, o.exit = .ret (r,s) := by
 rw [rep.1]
 cases ho : o.exit with
 | ret value =>
  rcases value with ⟨r,s⟩
  simp only [completed,ho,Bool.true_eq,true_iff,Exit.ret.injEq]
  exact ⟨r,s,rfl⟩
 | abort => simp [completed,ho]
 | diverge => simp [completed,ho]
#print axioms selected_true
#print axioms state_iff
end NNE_Observed
end
