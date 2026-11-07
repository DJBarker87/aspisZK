import PV_W5_DropLeaf
import PV_FN_SLICE_ValueCarrier
import PV_STX2_SliceF7
set_option autoImplicit false
noncomputable section
namespace PV_FN_SLICE_f7_Drop
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
/-- Internal cut AFTER f8 has returned, at the actual source178 drop. This is
not f7's call-entry Pre and supplies no callee success or live-result premise. -/
structure Cut where
  C : Carrier OWNER Data
  s : Store Data
  a : Nat
  parents : List PV_STX2_SliceMachine.Frame
  w : OWNER
  capture : Data

def source : Data := match PV_STX2_SliceF7.node4 with
  | .leaf (.drop _ _ fn _ _) => fn | _ => .null

def entry (x : Cut) : PV_W5_LeafBoundary.Entry :=
  {store := x.s,caller := x.a,parents := x.parents,loops := [],
   rest := PV_STX2_SliceF7.program.body.drop 5,arguments := [x.capture],destination := 0}

def effects (x : Cut) (changes : Address → Option Data) : Store Data :=
  PV_W5_DropLeaf.finalStore (PV_FN_SLICE_ValueCarrier.carrier x.C) (entry x)
    x.w x.capture changes

def reply (x : Cut) (H : PV_W5_NativeFrame.Backend) :=
  PV_STX2_Source7QUniformResourceHandler.lift H (.drop source x.capture) x.w

/-- All native answers and ALL argument-reachable store changes are retained.
The source read selecting capture is checked separately, not presumed here. -/
def Summary (x : Cut) (H : PV_W5_NativeFrame.Backend)
    (changes : Address → Option Data) : Prop :=
  PV_W5_DropLeaf.Post (PV_FN_SLICE_ValueCarrier.carrier x.C) (entry x) H
    x.w source x.capture changes ∧
  (effects x changes).nextActivation = x.s.nextActivation ∧
  PV_W1_OwnerWellFormed.OwnerWellFormed (reply x H).world (effects x changes).nextActivation ∧
  (reply x H).answer = (H (.drop source x.capture) (world x.w)).answer ∧
  (reply x H).events = (H (.drop source x.capture) (world x.w)).events

def Contract : Prop := ∀ (x : Cut) (H : PV_W5_NativeFrame.Backend)
    (changes : Address → Option Data),
  PV_W1_OwnerWellFormed.OwnerWellFormed x.w x.s.nextActivation → Summary x H changes

#check Contract
set_option pp.fullNames true in
set_option pp.proofs false in
#print Summary
end PV_FN_SLICE_f7_Drop
