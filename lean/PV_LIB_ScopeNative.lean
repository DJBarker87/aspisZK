import PV_LIB_NativeGraph
import PV_W1_NativeLeaves
set_option autoImplicit false
noncomputable section
namespace PV_LIB_ScopeNative
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame

def model269 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) :=
  PV_LIB_NativeGraph.model C (PV_W1_NativeLeaves.entry269 e args) H w events changes

def law269 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (out : PV_LIB.MachineObservation OWNER E) : Prop :=
  out = model269 C e H w args events changes

theorem certified269 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (pre : PV_W1_NativeLeaves.Pre e w) :
    law269 C e H w args events changes
      (PV_LIB.observe (PV_LIB_NativeGraph.internalModel C
        (PV_W1_NativeLeaves.entry269 e args) H w events changes)) ∧
      PV_W1_NativeLeaves.Post269 C e H w args events changes :=
  ⟨rfl,PV_W1_NativeLeaves.f269 C e H w args events changes pre⟩
#print axioms certified269

def model271 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) :=
  PV_LIB_NativeGraph.model C (PV_W1_NativeLeaves.entry271 e args) H w events changes

def law271 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (out : PV_LIB.MachineObservation OWNER E) : Prop :=
  out = model271 C e H w args events changes

theorem certified271 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (pre : PV_W1_NativeLeaves.Pre e w) :
    law271 C e H w args events changes
      (PV_LIB.observe (PV_LIB_NativeGraph.internalModel C
        (PV_W1_NativeLeaves.entry271 e args) H w events changes)) ∧
      PV_W1_NativeLeaves.Post271 C e H w args events changes :=
  ⟨rfl,PV_W1_NativeLeaves.f271 C e H w args events changes pre⟩
#print axioms certified271

def model14 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) :=
  PV_LIB_NativeGraph.model C (PV_W1_NativeLeaves.entry14 e args) H w events changes

def law14 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (out : PV_LIB.MachineObservation OWNER E) : Prop :=
  out = model14 C e H w args events changes

theorem certified14 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (pre : PV_W1_NativeLeaves.Pre e w) :
    law14 C e H w args events changes
      (PV_LIB.observe (PV_LIB_NativeGraph.internalModel C
        (PV_W1_NativeLeaves.entry14 e args) H w events changes)) ∧
      PV_W1_NativeLeaves.Post14 C e H w args events changes :=
  ⟨rfl,PV_W1_NativeLeaves.f14 C e H w args events changes pre⟩
#print axioms certified14

def model165 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) :=
  PV_LIB_NativeGraph.model C (PV_W1_NativeLeaves.entry165 e args) H w events changes

def law165 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (out : PV_LIB.MachineObservation OWNER E) : Prop :=
  out = model165 C e H w args events changes

theorem certified165 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (pre : PV_W1_NativeLeaves.Pre e w) :
    law165 C e H w args events changes
      (PV_LIB.observe (PV_LIB_NativeGraph.internalModel C
        (PV_W1_NativeLeaves.entry165 e args) H w events changes)) ∧
      PV_W1_NativeLeaves.Post165 C e H w args events changes :=
  ⟨rfl,PV_W1_NativeLeaves.f165 C e H w args events changes pre⟩
#print axioms certified165

def model168 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) :=
  PV_LIB_NativeGraph.model C (PV_W1_NativeLeaves.entry168 e args) H w events changes

def law168 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (out : PV_LIB.MachineObservation OWNER E) : Prop :=
  out = model168 C e H w args events changes

theorem certified168 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (pre : PV_W1_NativeLeaves.Pre e w) :
    law168 C e H w args events changes
      (PV_LIB.observe (PV_LIB_NativeGraph.internalModel C
        (PV_W1_NativeLeaves.entry168 e args) H w events changes)) ∧
      PV_W1_NativeLeaves.Post168 C e H w args events changes :=
  ⟨rfl,PV_W1_NativeLeaves.f168 C e H w args events changes pre⟩
#print axioms certified168

def model7 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) :=
  PV_LIB_NativeGraph.model C (PV_W1_NativeLeaves.entry7 e args) H w events changes

def law7 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (out : PV_LIB.MachineObservation OWNER E) : Prop :=
  out = model7 C e H w args events changes

theorem certified7 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (pre : PV_W1_NativeLeaves.Pre e w) :
    law7 C e H w args events changes
      (PV_LIB.observe (PV_LIB_NativeGraph.internalModel C
        (PV_W1_NativeLeaves.entry7 e args) H w events changes)) ∧
      PV_W1_NativeLeaves.Post7 C e H w args events changes :=
  ⟨rfl,PV_W1_NativeLeaves.f7 C e H w args events changes pre⟩
#print axioms certified7

def model8 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) :=
  PV_LIB_NativeGraph.model C (PV_W1_NativeLeaves.entry8 e args) H w events changes

def law8 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (out : PV_LIB.MachineObservation OWNER E) : Prop :=
  out = model8 C e H w args events changes

theorem certified8 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (pre : PV_W1_NativeLeaves.Pre e w) :
    law8 C e H w args events changes
      (PV_LIB.observe (PV_LIB_NativeGraph.internalModel C
        (PV_W1_NativeLeaves.entry8 e args) H w events changes)) ∧
      PV_W1_NativeLeaves.Post8 C e H w args events changes :=
  ⟨rfl,PV_W1_NativeLeaves.f8 C e H w args events changes pre⟩
#print axioms certified8
end PV_LIB_ScopeNative
