import PV_LIB_Observation
import PV_W1_TLSLeaves
set_option autoImplicit false
noncomputable section
namespace PV_LIB_ThreadNamed
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame

def internalModel {E : Type} (C : Carrier OWNER Data) (d : Entry)
    (H : Backend E) (w : OWNER) (events : List E) :=
  deliver C d (PV_THR2_OwnUniformResourceHandler.lift H
    (.child d.callee d.store.nextActivation d.arguments) w) events

def model123 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E) :=
  PV_LIB.observe (internalModel C (PV_W1_NamedLeafBoundary.entry e (PV_W1_NamedLeafBoundary.function PV_THR2_F6.node20) args) H w events)
def law123 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (out : PV_LIB.MachineObservation OWNER E) : Prop := out = model123 C e H w args events

theorem certified123 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (pre : PV_W1_ClosedLeaves.Pre e w) :
    law123 C e H w args events (PV_LIB.observe (internalModel C
      (PV_W1_NamedLeafBoundary.entry e (PV_W1_NamedLeafBoundary.function PV_THR2_F6.node20) args) H w events)) ∧
    PV_W1_ClosedLeaves.Post123 C e H w args events :=
  ⟨rfl,PV_W1_ClosedLeaves.f123 C e H w args events pre⟩
#print axioms certified123

def model18 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E) :=
  PV_LIB.observe (internalModel C (PV_W1_NamedLeafBoundary.entry e (PV_THR2_F2Call.descriptors.2) args) H w events)
def law18 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (out : PV_LIB.MachineObservation OWNER E) : Prop := out = model18 C e H w args events

theorem certified18 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (pre : PV_W1_ClosedLeaves.Pre e w) :
    law18 C e H w args events (PV_LIB.observe (internalModel C
      (PV_W1_NamedLeafBoundary.entry e (PV_THR2_F2Call.descriptors.2) args) H w events)) ∧
    PV_W1_ClosedLeaves.Post18 C e H w args events :=
  ⟨rfl,PV_W1_ClosedLeaves.f18 C e H w args events pre⟩
#print axioms certified18

def model468 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E) :=
  PV_LIB.observe (internalModel C (PV_W1_NamedLeafBoundary.entry e ((PV_THR2_KeyValues.castToken true).2) args) H w events)
def law468 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (out : PV_LIB.MachineObservation OWNER E) : Prop := out = model468 C e H w args events

theorem certified468 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (pre : PV_W1_ClosedLeaves.Pre e w) :
    law468 C e H w args events (PV_LIB.observe (internalModel C
      (PV_W1_NamedLeafBoundary.entry e ((PV_THR2_KeyValues.castToken true).2) args) H w events)) ∧
    PV_W1_TLSLeaves.Post true C e H w args events :=
  ⟨rfl,PV_W1_TLSLeaves.f468 C e H w args events pre⟩
#print axioms certified468

def model469 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E) :=
  PV_LIB.observe (internalModel C (PV_W1_NamedLeafBoundary.entry e ((PV_THR2_KeyValues.castToken false).2) args) H w events)
def law469 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (out : PV_LIB.MachineObservation OWNER E) : Prop := out = model469 C e H w args events

theorem certified469 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (pre : PV_W1_ClosedLeaves.Pre e w) :
    law469 C e H w args events (PV_LIB.observe (internalModel C
      (PV_W1_NamedLeafBoundary.entry e ((PV_THR2_KeyValues.castToken false).2) args) H w events)) ∧
    PV_W1_TLSLeaves.Post false C e H w args events :=
  ⟨rfl,PV_W1_TLSLeaves.f469 C e H w args events pre⟩
#print axioms certified469
end PV_LIB_ThreadNamed
