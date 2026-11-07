import PV_LIB_NativeGraph
import PV_W1_NativeLeaves
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SpawnNative
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame

def model213 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) :=
  PV_LIB_NativeGraph.model C (PV_W1_NativeLeaves.entry213 e args) H w events changes

def law213 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (out : PV_LIB.MachineObservation OWNER E) : Prop :=
  out = model213 C e H w args events changes

theorem certified213 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (pre : PV_W1_NativeLeaves.Pre e w) :
    law213 C e H w args events changes
      (PV_LIB.observe (PV_LIB_NativeGraph.internalModel C
        (PV_W1_NativeLeaves.entry213 e args) H w events changes)) ∧
      PV_W1_NativeLeaves.Post213 C e H w args events changes :=
  ⟨rfl,PV_W1_NativeLeaves.f213 C e H w args events changes pre⟩
#print axioms certified213

def model295 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) :=
  PV_LIB_NativeGraph.model C (PV_W1_NativeLeaves.entry295 e args) H w events changes

def law295 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (out : PV_LIB.MachineObservation OWNER E) : Prop :=
  out = model295 C e H w args events changes

theorem certified295 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (pre : PV_W1_NativeLeaves.Pre e w) :
    law295 C e H w args events changes
      (PV_LIB.observe (PV_LIB_NativeGraph.internalModel C
        (PV_W1_NativeLeaves.entry295 e args) H w events changes)) ∧
      PV_W1_NativeLeaves.Post295 C e H w args events changes :=
  ⟨rfl,PV_W1_NativeLeaves.f295 C e H w args events changes pre⟩
#print axioms certified295

def model452 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) :=
  PV_LIB_NativeGraph.model C (PV_W1_NativeLeaves.entry452 e args) H w events changes

def law452 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (out : PV_LIB.MachineObservation OWNER E) : Prop :=
  out = model452 C e H w args events changes

theorem certified452 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (pre : PV_W1_NativeLeaves.Pre e w) :
    law452 C e H w args events changes
      (PV_LIB.observe (PV_LIB_NativeGraph.internalModel C
        (PV_W1_NativeLeaves.entry452 e args) H w events changes)) ∧
      PV_W1_NativeLeaves.Post452 C e H w args events changes :=
  ⟨rfl,PV_W1_NativeLeaves.f452 C e H w args events changes pre⟩
#print axioms certified452

def model453 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) :=
  PV_LIB_NativeGraph.model C (PV_W1_NativeLeaves.entry453 e args) H w events changes

def law453 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (out : PV_LIB.MachineObservation OWNER E) : Prop :=
  out = model453 C e H w args events changes

theorem certified453 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (pre : PV_W1_NativeLeaves.Pre e w) :
    law453 C e H w args events changes
      (PV_LIB.observe (PV_LIB_NativeGraph.internalModel C
        (PV_W1_NativeLeaves.entry453 e args) H w events changes)) ∧
      PV_W1_NativeLeaves.Post453 C e H w args events changes :=
  ⟨rfl,PV_W1_NativeLeaves.f453 C e H w args events changes pre⟩
#print axioms certified453

def model454 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) :=
  PV_LIB_NativeGraph.model C (PV_W1_NativeLeaves.entry454 e args) H w events changes

def law454 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (out : PV_LIB.MachineObservation OWNER E) : Prop :=
  out = model454 C e H w args events changes

theorem certified454 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (pre : PV_W1_NativeLeaves.Pre e w) :
    law454 C e H w args events changes
      (PV_LIB.observe (PV_LIB_NativeGraph.internalModel C
        (PV_W1_NativeLeaves.entry454 e args) H w events changes)) ∧
      PV_W1_NativeLeaves.Post454 C e H w args events changes :=
  ⟨rfl,PV_W1_NativeLeaves.f454 C e H w args events changes pre⟩
#print axioms certified454

def model455 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) :=
  PV_LIB_NativeGraph.model C (PV_W1_NativeLeaves.entry455 e args) H w events changes

def law455 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (out : PV_LIB.MachineObservation OWNER E) : Prop :=
  out = model455 C e H w args events changes

theorem certified455 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (pre : PV_W1_NativeLeaves.Pre e w) :
    law455 C e H w args events changes
      (PV_LIB.observe (PV_LIB_NativeGraph.internalModel C
        (PV_W1_NativeLeaves.entry455 e args) H w events changes)) ∧
      PV_W1_NativeLeaves.Post455 C e H w args events changes :=
  ⟨rfl,PV_W1_NativeLeaves.f455 C e H w args events changes pre⟩
#print axioms certified455

def model456 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) :=
  PV_LIB_NativeGraph.model C (PV_W1_NativeLeaves.entry456 e args) H w events changes

def law456 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (out : PV_LIB.MachineObservation OWNER E) : Prop :=
  out = model456 C e H w args events changes

theorem certified456 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (pre : PV_W1_NativeLeaves.Pre e w) :
    law456 C e H w args events changes
      (PV_LIB.observe (PV_LIB_NativeGraph.internalModel C
        (PV_W1_NativeLeaves.entry456 e args) H w events changes)) ∧
      PV_W1_NativeLeaves.Post456 C e H w args events changes :=
  ⟨rfl,PV_W1_NativeLeaves.f456 C e H w args events changes pre⟩
#print axioms certified456

def model457 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) :=
  PV_LIB_NativeGraph.model C (PV_W1_NativeLeaves.entry457 e args) H w events changes

def law457 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (out : PV_LIB.MachineObservation OWNER E) : Prop :=
  out = model457 C e H w args events changes

theorem certified457 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (pre : PV_W1_NativeLeaves.Pre e w) :
    law457 C e H w args events changes
      (PV_LIB.observe (PV_LIB_NativeGraph.internalModel C
        (PV_W1_NativeLeaves.entry457 e args) H w events changes)) ∧
      PV_W1_NativeLeaves.Post457 C e H w args events changes :=
  ⟨rfl,PV_W1_NativeLeaves.f457 C e H w args events changes pre⟩
#print axioms certified457

def model459 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) :=
  PV_LIB_NativeGraph.model C (PV_W1_NativeLeaves.entry459 e args) H w events changes

def law459 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (out : PV_LIB.MachineObservation OWNER E) : Prop :=
  out = model459 C e H w args events changes

theorem certified459 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (pre : PV_W1_NativeLeaves.Pre e w) :
    law459 C e H w args events changes
      (PV_LIB.observe (PV_LIB_NativeGraph.internalModel C
        (PV_W1_NativeLeaves.entry459 e args) H w events changes)) ∧
      PV_W1_NativeLeaves.Post459 C e H w args events changes :=
  ⟨rfl,PV_W1_NativeLeaves.f459 C e H w args events changes pre⟩
#print axioms certified459
end PV_LIB_SpawnNative
