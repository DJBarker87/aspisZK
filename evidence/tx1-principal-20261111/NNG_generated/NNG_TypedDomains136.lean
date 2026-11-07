import NNG_LIBClaimsDomain
import NNG_LIBRecordReached
import NNG_TraceAll136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_TypedDomains136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NNG_LIBScalar NNG_LIBArrayDomain NNG_LIBClaimsDomain

/-- A reached typed argument is checked at its literal lexical site. Replies
are retained by Event, without being assumed successful by this predicate. -/
def atArgs {A : Type} (site : String) (P : A → Prop) (event : NMT_CallTree.Event) : Prop :=
  match event with
  | @NMT_CallTree.Event.call Args _ tag args _ => tag=site → ∀ h : Args=A,P (cast h args)

theorem same {A B : Type} (site : String) (P : A → Prop) (a : A) (r : Result B) :
    atArgs site P (.call site a r) ↔ P a := by
  simp [atArgs]
#print axioms same

theorem other {A Args B : Type} (site tag : String) (P : A → Prop) (args : Args) (r : Result B)
    (different : tag≠site) : atArgs site P (.call tag args r) := by
  intro equal
  exact (different equal).elim
#print axioms other

def terminal (args : Public × Claims × Alpha × aspis_core.state_only_prefix.r0.Challenges) : Prop :=
  DomainClaims args.2.1 ∧ DomainArray args.2.2.1
def mask (args : Array Q 16#usize × Alpha × Q × Alpha) : Prop :=
  DomainArray args.1 ∧ DomainArray args.2.1 ∧ Domain args.2.2.1 ∧ DomainArray args.2.2.2
def arithmetic (args : Q × Q) : Prop := Domain args.1 ∧ Domain args.2
def circle (args : r1_wire.SemanticTranscript Unit × r1_wire.ValidatedRecord) : Prop :=
  args.2.framed.val.length≤3717
def decode (args : r1_wire.ValidatedRecord × Usize) : Prop := LIB_VDecode.Domain (toT14 args.1) args.2.val

structure Checked (event : NMT_CallTree.Event) : Prop where
  terminal : atArgs "terminal" terminal event
  mask : atArgs "mask" mask event
  multiply : atArgs "multiply" arithmetic event
  addMask : atArgs "addMask" arithmetic event
  addExtra : atArgs "addExtra" arithmetic event
  circle0 : atArgs "circle0" circle event
  circle1 : atArgs "circle1" circle event
  extra : atArgs "extra" decode event
  beforeZ1 : atArgs "beforeZ1" decode event
end AspisR1.NNG_TypedDomains136
