import PV_LIB_NativeGraph
import PV_W1_NativeLeaves
set_option autoImplicit false
noncomputable section
namespace PV_LIB_RootNative
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame

def model3 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) :=
  PV_LIB_NativeGraph.model C (PV_W1_NativeLeaves.entry3 e args) H w events changes

def law3 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (out : PV_LIB.MachineObservation OWNER E) : Prop :=
  out = model3 C e H w args events changes

theorem certified3 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (pre : PV_W1_NativeLeaves.Pre e w) :
    law3 C e H w args events changes
      (PV_LIB.observe (PV_LIB_NativeGraph.internalModel C
        (PV_W1_NativeLeaves.entry3 e args) H w events changes)) ∧
      PV_W1_NativeLeaves.Post3 C e H w args events changes :=
  ⟨rfl,PV_W1_NativeLeaves.f3 C e H w args events changes pre⟩
#print axioms certified3

def model4 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) :=
  PV_LIB_NativeGraph.model C (PV_W1_NativeLeaves.entry4 e args) H w events changes

def law4 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (out : PV_LIB.MachineObservation OWNER E) : Prop :=
  out = model4 C e H w args events changes

theorem certified4 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (pre : PV_W1_NativeLeaves.Pre e w) :
    law4 C e H w args events changes
      (PV_LIB.observe (PV_LIB_NativeGraph.internalModel C
        (PV_W1_NativeLeaves.entry4 e args) H w events changes)) ∧
      PV_W1_NativeLeaves.Post4 C e H w args events changes :=
  ⟨rfl,PV_W1_NativeLeaves.f4 C e H w args events changes pre⟩
#print axioms certified4

def model171 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) :=
  PV_LIB_NativeGraph.model C (PV_W1_NativeLeaves.entry171 e args) H w events changes

def law171 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (out : PV_LIB.MachineObservation OWNER E) : Prop :=
  out = model171 C e H w args events changes

theorem certified171 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (pre : PV_W1_NativeLeaves.Pre e w) :
    law171 C e H w args events changes
      (PV_LIB.observe (PV_LIB_NativeGraph.internalModel C
        (PV_W1_NativeLeaves.entry171 e args) H w events changes)) ∧
      PV_W1_NativeLeaves.Post171 C e H w args events changes :=
  ⟨rfl,PV_W1_NativeLeaves.f171 C e H w args events changes pre⟩
#print axioms certified171

def model268 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) :=
  PV_LIB_NativeGraph.model C (PV_W1_NativeLeaves.entry268 e args) H w events changes

def law268 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (out : PV_LIB.MachineObservation OWNER E) : Prop :=
  out = model268 C e H w args events changes

theorem certified268 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (pre : PV_W1_NativeLeaves.Pre e w) :
    law268 C e H w args events changes
      (PV_LIB.observe (PV_LIB_NativeGraph.internalModel C
        (PV_W1_NativeLeaves.entry268 e args) H w events changes)) ∧
      PV_W1_NativeLeaves.Post268 C e H w args events changes :=
  ⟨rfl,PV_W1_NativeLeaves.f268 C e H w args events changes pre⟩
#print axioms certified268
end PV_LIB_RootNative
