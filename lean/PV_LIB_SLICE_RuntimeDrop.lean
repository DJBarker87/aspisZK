import PV_LIB_Observation
import PV_FN_SLICE_f7_RuntimeDrop
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SLICE_RuntimeDrop
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
abbrev Input := PV_FN_SLICE_f7_RuntimeDrop.Input

/-- Exact source178 entry after f8 has delivered; this is not f7's own entry. -/
def start (x : Input) : PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent :=
  ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF7.program.body.drop 4},
    x.parent :: x.parents,x.s⟩,x.w,x.es⟩,x.stack⟩

def reply (x : Input) (capture : Data) :=
  x.H (.drop PV_FN_SLICE_f7_AfterDrop.source.1 capture) x.w

def steps (x : Input) (capture : Data) : Nat :=
  1+1+PV_FN_SLICE_f7_AfterDrop.steps (reply x capture)

/-- Full-reply deterministic suffix, including failure, divergence, fault and
pending. Public abort observations retain only the exact event prefix. -/
def model (x : Input) (capture : Data) :=
  PV_LIB.observe (PV_FN_SLICE_f7_AfterDrop.finish x capture (reply x capture))

def law (x : Input) (capture : Data)
    (out : PV_LIB.MachineObservation OWNER PV_RJ4IDB.NativeEvent) : Prop :=
  out = model x capture

/-- The unchanged provider discharges the Drop owner/frame requirement using
its typed-f22 projection. No per-call identity effect or successful reply is
assumed. The remaining premises are the literal source178 entry cells and
saved caller action, and the existing named machine Drop semantics. -/
theorem certified (x : Input) (capture : Data)
    (spec : PV_FN_SLICE_RuntimeBindings.DropSemantics x.H)
    (cell : x.s.cells ⟨x.a,1,[]⟩ = some capture)
    (value : x.s.cells ⟨x.a,0,[]⟩ = some x.ptr)
    (saved : x.parent.waiting = some x.wait)
    (action : x.wait.action = .child x.a (.local x.dest))
    (pre : PV_W1_OwnerWellFormed.OwnerWellFormed x.w x.s.nextActivation) :
    law x capture (PV_LIB.observe
      (PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C)
        x.K x.P x.H (steps x capture) (start x))) :=
  congrArg PV_LIB.observe
    (PV_FN_SLICE_f7_RuntimeDrop.run x capture spec cell value saved action pre)

theorem functional (x : Input) (capture : Data)
    (left right : PV_LIB.MachineObservation OWNER PV_RJ4IDB.NativeEvent)
    (hl : law x capture left) (hr : law x capture right) : left = right :=
  hl.trans hr.symm

/-- The full installed runtime stack supplies the named Drop semantics;
resources and fallback remain the actual explicit environment channels. -/
theorem installed (base : Carrier PV_STX_World.World Data) (ctrl : Control)
    (resources : PV_EVHB_OWNER.Resources) (encode : PV_EVHB_OWNER.Encode)
    {s : OWNER} {value : PV_STX2_Source7EntryOwned.Foundation}
    (entry : PV_STX2_Source7EntryOwned.Source7EntryOwned s value)
    (external : Nat → PV_STX_World.World → Reply PV_STX_World.World PV_RJ4IDB.NativeEvent Unit)
    (fallback : PV_W5_NativeFrame.Backend) :
    PV_FN_SLICE_RuntimeBindings.DropSemantics
      (PV_STX2_Source7QUniformInstalledHandler.handler base ctrl resources encode entry external fallback) :=
  PV_FN_SLICE_RuntimeBindings.installed_drop base ctrl resources encode entry external fallback

#print axioms certified
#print axioms functional
#print axioms installed
end PV_LIB_SLICE_RuntimeDrop
