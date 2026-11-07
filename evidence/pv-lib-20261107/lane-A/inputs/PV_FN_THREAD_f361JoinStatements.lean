import PV_FN_THREAD_f361Statement
import PV_FN_THREAD_f361Call124
set_option autoImplicit false
noncomputable section

namespace PV_FN_THREAD_f361JoinStatements
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_FN_THREAD_f361

/-- Local context invariant at the SELECTED trace cut, not an assumed
invariant over every reachable control configuration. -/
def Context (x : Input) (q : State) : Prop :=
  PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed q.current.world
    (PV_W1_LeafBoundary.statusStore q.current.status).nextActivation ∧
  x.a < (PV_W1_LeafBoundary.statusStore q.current.status).nextActivation ∧
  ∀ c, q.current.status = .running c → c.frame.activation = x.a →
    c.callers = x.parent :: x.parents

/-- A cumulative own-entry cut retains its particular finite certificate. -/
def Cut (x : Input) (offset : Nat) : Prop :=
  ∃ (q : State) (_run : Run x (entry x) q), Context x q ∧
    (Finished x q ∨ At x (PV_THR2_F361.live.body.drop offset) q)

/-- The provider Pre is a conclusion at the ACTUAL selected12801 cut. -/
def Cut124 (x : Input) : Prop :=
  ∃ (q : State) (_run : Run x (entry x) q), Context x q ∧
    (Finished x q ∨ At x (PV_THR2_F361.live.body.drop 58) q) ∧
    (At x (PV_THR2_F361.live.body.drop 58) q →
      ∃ e, AtCall x q e ∧ e.callee = PV_FN_THREAD_f361Call124.fn ∧
        e.destination = 17 ∧
        PV_FN_THREAD_f124.Pre (input124 x e q.current.world q.current.events))

def OwnedCuts (x : Input) : Prop :=
  ∃ (q : State) (run : Run x (entry x) q), Context x q ∧
    (Finished x q ∨ At x (PV_THR2_F361.live.body.drop 130) q) ∧ Checked run

def ReturnedCut (x : Input) : Prop :=
  ∃ (q : State) (run : Run x (entry x) q), Finished x q ∧ Checked run

def FramedReturn (x : Input) : Prop :=
  ∃ (q : State) (run : Run x (entry x) q), Finished x q ∧ Frame x q ∧ Checked run

/-- Named resource validity is separate from DocumentedFacts. It is the
existing FreshAllocationValidity' at actual reachable pre-worlds, with every
resource answer retained. It assumes no returned allocator or decoder case. -/
def AllocationValidity (x : Input) : Prop :=
  ∀ q, Execution x (entry x) q →
    PV_OWN2_FreshAllocationRefinement.FreshAllocationValidity' x.resources x.granted q.current.world

/- These are exact theorem TYPES, not axioms, admitted theorems or dependency
arguments. The proof modules must inhabit them in the following order. -/

def own_entry_to124_statement : Prop :=
  ∀ (x : Input), Pre x → DocumentedFacts x → Cut124 x

def call124_join_statement : Prop :=
  ∀ (x : Input), Pre x →
    PV_FN_THREAD_f361Provider124.Dependency → DocumentedFacts x →
    Cut124 x → Cut x 59

def constructor_clone_join_from_entry_statement : Prop :=
  ∀ (x : Input), Pre x → DocumentedFacts x → Cut x 59 → Cut x 81

def packet126_join_statement : Prop :=
  ∀ (x : Input), Pre x → DocumentedFacts x → Cut x 81 → Cut x 84

def scope126_join_statement : Prop :=
  ∀ (x : Input), Pre x → DocumentedFacts x → Cut x 84 → Cut x 92

def box_join_statement : Prop :=
  ∀ (x : Input), Pre x → DocumentedFacts x →
    AllocationValidity x → Cut x 92 → Cut x 113

def owninit_join_statement : Prop :=
  ∀ (x : Input), Pre x → DocumentedFacts x → AllocationValidity x →
    Cut x 113 → Cut x 130 ∧ OwnedCuts x

def return_join_statement : Prop :=
  ∀ (x : Input), Pre x → DocumentedFacts x →
    Cut x 130 → OwnedCuts x → ReturnedCut x ∧ OwnedCuts x

def full_frame_statement : Prop :=
  ∀ (x : Input), Pre x → DocumentedFacts x →
    ReturnedCut x → FramedReturn x

def assemble_statement : Prop :=
  ∀ (x : Input), FramedReturn x → OwnedCuts x → Post x

#print own_entry_to124_statement
#print call124_join_statement
#print constructor_clone_join_from_entry_statement
#print packet126_join_statement
#print scope126_join_statement
#print box_join_statement
#print owninit_join_statement
#print return_join_statement
#print full_frame_statement
#print assemble_statement
#print axioms own_entry_to124_statement
#print axioms call124_join_statement
#print axioms constructor_clone_join_from_entry_statement
#print axioms packet126_join_statement
#print axioms scope126_join_statement
#print axioms box_join_statement
#print axioms owninit_join_statement
#print axioms return_join_statement
#print axioms full_frame_statement
#print axioms assemble_statement
end PV_FN_THREAD_f361JoinStatements
