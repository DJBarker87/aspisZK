import PV_LIB_A_C18_NativeGraph
import PV_W1_NativeLeaves
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_NativeLeaves
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame

def model277 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) :=
  PV_LIB_NativeGraph.model C (PV_W1_NativeLeaves.entry277 e args) H w events changes

def law277 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (out : PV_LIB.MachineObservation OWNER E) : Prop :=
  out = model277 C e H w args events changes

theorem certified277 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (pre : PV_W1_NativeLeaves.Pre e w) :
    law277 C e H w args events changes
      (PV_LIB.observe (PV_LIB_NativeGraph.internalModel C
        (PV_W1_NativeLeaves.entry277 e args) H w events changes)) ∧
      PV_W1_NativeLeaves.Post277 C e H w args events changes :=
  ⟨rfl,PV_W1_NativeLeaves.f277 C e H w args events changes pre⟩
#print axioms certified277

def model278 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) :=
  PV_LIB_NativeGraph.model C (PV_W1_NativeLeaves.entry278 e args) H w events changes

def law278 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (out : PV_LIB.MachineObservation OWNER E) : Prop :=
  out = model278 C e H w args events changes

theorem certified278 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (pre : PV_W1_NativeLeaves.Pre e w) :
    law278 C e H w args events changes
      (PV_LIB.observe (PV_LIB_NativeGraph.internalModel C
        (PV_W1_NativeLeaves.entry278 e args) H w events changes)) ∧
      PV_W1_NativeLeaves.Post278 C e H w args events changes :=
  ⟨rfl,PV_W1_NativeLeaves.f278 C e H w args events changes pre⟩
#print axioms certified278

def model279 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) :=
  PV_LIB_NativeGraph.model C (PV_W1_NativeLeaves.entry279 e args) H w events changes

def law279 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (out : PV_LIB.MachineObservation OWNER E) : Prop :=
  out = model279 C e H w args events changes

theorem certified279 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (pre : PV_W1_NativeLeaves.Pre e w) :
    law279 C e H w args events changes
      (PV_LIB.observe (PV_LIB_NativeGraph.internalModel C
        (PV_W1_NativeLeaves.entry279 e args) H w events changes)) ∧
      PV_W1_NativeLeaves.Post279 C e H w args events changes :=
  ⟨rfl,PV_W1_NativeLeaves.f279 C e H w args events changes pre⟩
#print axioms certified279

def model280 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) :=
  PV_LIB_NativeGraph.model C (PV_W1_NativeLeaves.entry280 e args) H w events changes

def law280 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (out : PV_LIB.MachineObservation OWNER E) : Prop :=
  out = model280 C e H w args events changes

theorem certified280 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (pre : PV_W1_NativeLeaves.Pre e w) :
    law280 C e H w args events changes
      (PV_LIB.observe (PV_LIB_NativeGraph.internalModel C
        (PV_W1_NativeLeaves.entry280 e args) H w events changes)) ∧
      PV_W1_NativeLeaves.Post280 C e H w args events changes :=
  ⟨rfl,PV_W1_NativeLeaves.f280 C e H w args events changes pre⟩
#print axioms certified280

def model612 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) :=
  PV_LIB_NativeGraph.model C (PV_W1_NativeLeaves.entry612 e args) H w events changes

def law612 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (out : PV_LIB.MachineObservation OWNER E) : Prop :=
  out = model612 C e H w args events changes

theorem certified612 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (pre : PV_W1_NativeLeaves.Pre e w) :
    law612 C e H w args events changes
      (PV_LIB.observe (PV_LIB_NativeGraph.internalModel C
        (PV_W1_NativeLeaves.entry612 e args) H w events changes)) ∧
      PV_W1_NativeLeaves.Post612 C e H w args events changes :=
  ⟨rfl,PV_W1_NativeLeaves.f612 C e H w args events changes pre⟩
#print axioms certified612

end PV_LIB_A_NativeLeaves
