import PV_STX2_Source7QHeaderAssociation
set_option autoImplicit false
noncomputable section
namespace PV_STX2_Source7QHeaderStep
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_EVHB_OWNER PV_STX2_SliceMachine
/-- Conditional on owner acceptance of the translator patch. The exact source
RawVecInner aggregate tag, used by the q header binding at f35/s1417. -/
def kind : Data := match PV_STX2_Source7CtorF35.node140 with
  | .leaf (.aggregateMove _ _ k _) => k
  | _ => .null
/-- Conditional on owner acceptance of the translator patch. Interpret only
RawVecInner's source three-field aggregate in addition to existing field slots.
Needed for the native aggregate to succeed before the q ghost header update. -/
def carrier (base : Carrier OWNER Data) : Carrier OWNER Data :=
  {PV_STX2_Aggregates.carrier base with aggregate := fun tag args =>
    if PV_STX2_Source7QHeaderBinding.rawInner tag then match args with
      | [_,_,_] => some (PV_STX2_Aggregates.pack tag args)
      | _ => none
    else (PV_STX2_Aggregates.carrier base).aggregate tag args}
/-- Conditional on owner acceptance of the translator patch. Exact source
moves into the RawVecInner result local; no OWNER header or id is inserted here. -/
def stored (s : Store Data) (a : Nat) (ptr cap alloc : Data) : Store Data :=
  write (write (write (write s ⟨a,17,[]⟩ none) ⟨a,19,[]⟩ none) ⟨a,20,[]⟩ none)
    ⟨a,16,[]⟩ (some (PV_STX2_Aggregates.pack kind [ptr,cap,alloc]))
/-- Conditional on owner acceptance of the translator patch. New local
binding interpretation: only a successful native step applies the source-bound
header stores. Every other native terminal retains its exact world and events. -/
def step {E : Type} (base : Carrier OWNER Data) (control : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (target : Option PV_EVHB_OWNER.Place) (c : Config) (w : OWNER) : Prefix OWNER E :=
  let p := PV_STX2_SliceMachine.step (carrier base) control programs handler c w
  match p.status with
  | .running _ => {p with world := PV_STX2_Source7QHeaderBinding.binding (carrier base) target c p.world}
  | _ => p
/-- Conditional on owner acceptance of the translator patch. Execute the
actual f35/s1417 aggregate and its header binding together. Required by q's
return path; pre-instruction pointer/capacity locals are explicit store-cut
inputs, still to be derived from the allocation reply by full composition. -/
theorem allocated_step {E : Type} (base : Carrier OWNER Data) (control : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (parents : List Frame) (after : List PV_STX2_SliceSyntax.Node)
    (a pointer cap : Nat) (ptr alloc : Data) (w : OWNER)
    (target : Option PV_EVHB_OWNER.Place)
    (p : s.cells ⟨a,17,[]⟩ = some ptr)
    (n : s.cells ⟨a,19,[]⟩ = some (.number cap))
    (al : s.cells ⟨a,20,[]⟩ = some alloc)
    (field : (carrier base).field ptr 0 = some (.number pointer)) :
    step base control programs handler target
      ⟨{activation := a,remaining := PV_STX2_Source7CtorF35.node140 :: after},parents,s⟩ w =
      ⟨.running ⟨{activation := a,remaining := after},parents,
        stored s a ptr (.number cap) alloc⟩,
        PV_STX2_Source7QHeaderBinding.install target pointer cap w,[]⟩ := by
  have bind := PV_STX2_Source7QHeaderBinding.allocated_binding
    (carrier base) s parents after a pointer cap ptr alloc w target p n al field
  simp [step,PV_STX2_SliceMachine.step,PV_STX2_Source7CtorF35.node140,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operands,operand,
    PV_STX2_Store.read,locate,writeAddress,write,p,n,al,carrier,
    PV_STX2_Source7QHeaderBinding.rawInner,stored,kind] at *
  exact bind
#print axioms kind
#print axioms carrier
#print axioms stored
#print axioms step
#print axioms allocated_step
end PV_STX2_Source7QHeaderStep
