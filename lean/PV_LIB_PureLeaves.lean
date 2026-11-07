import PV_LIB_LeafObservation
set_option autoImplicit false
noncomputable section
namespace PV_LIB_PureLeaves
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame
/-- These fields are exactly the deterministic functions in CLOSED roots.
The provider Post is a certificate, never the child law. Native binding to
an original caller machine remains its named documented-semantics obligation. -/

def model217 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (input : Data) :=
  PV_LIB.leafObserve (PV_W1_F217.call e.store (PV_THR2_OwnUniformResourceHandler.lift H) w e.store.nextActivation input)
def law217 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (input : Data)
    (out : PV_LIB.Observation (Answer Data) (Store Data × OWNER) E) : Prop :=
  out = model217 C e H w input

theorem certified217 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (input : Data) (events : List E)
    (pre : PV_W1_ClosedLeaves.Pre e w) :
    law217 C e H w input (PV_LIB.leafObserve (PV_W1_F217.call e.store (PV_THR2_OwnUniformResourceHandler.lift H) w e.store.nextActivation input)) ∧
      PV_W1_ClosedLeaves.Post217 C e H w input events :=
  ⟨rfl,PV_W1_ClosedLeaves.f217 C e H w input events pre⟩
#print axioms certified217

def model312 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (input : Data) :=
  PV_LIB.leafObserve (PV_W1_F312.call e.store (PV_THR2_OwnUniformResourceHandler.lift H) w e.store.nextActivation input)
def law312 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (input : Data)
    (out : PV_LIB.Observation (Answer Data) (Store Data × OWNER) E) : Prop :=
  out = model312 C e H w input

theorem certified312 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (input : Data) (events : List E)
    (pre : PV_W1_ClosedLeaves.Pre e w) :
    law312 C e H w input (PV_LIB.leafObserve (PV_W1_F312.call e.store (PV_THR2_OwnUniformResourceHandler.lift H) w e.store.nextActivation input)) ∧
      PV_W1_ClosedLeaves.Post312 C e H w input events :=
  ⟨rfl,PV_W1_ClosedLeaves.f312 C e H w input events pre⟩
#print axioms certified312

def model313 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (input : Data) :=
  PV_LIB.leafObserve (PV_W1_F313.call e.store (PV_THR2_OwnUniformResourceHandler.lift H) w e.store.nextActivation input)
def law313 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (input : Data)
    (out : PV_LIB.Observation (Answer Data) (Store Data × OWNER) E) : Prop :=
  out = model313 C e H w input

theorem certified313 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (input : Data) (events : List E)
    (pre : PV_W1_ClosedLeaves.Pre e w) :
    law313 C e H w input (PV_LIB.leafObserve (PV_W1_F313.call e.store (PV_THR2_OwnUniformResourceHandler.lift H) w e.store.nextActivation input)) ∧
      PV_W1_ClosedLeaves.Post313 C e H w input events :=
  ⟨rfl,PV_W1_ClosedLeaves.f313 C e H w input events pre⟩
#print axioms certified313

def model320 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (input : Data) :=
  PV_LIB.leafObserve (PV_W1_F320.call C e.store (PV_THR2_OwnUniformResourceHandler.lift H) w e.store.nextActivation input)
def law320 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (input : Data)
    (out : PV_LIB.Observation (Answer Data) (Store Data × OWNER) E) : Prop :=
  out = model320 C e H w input

theorem certified320 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (input : Data) (events : List E)
    (pre : PV_W1_ClosedLeaves.Pre e w) :
    law320 C e H w input (PV_LIB.leafObserve (PV_W1_F320.call C e.store (PV_THR2_OwnUniformResourceHandler.lift H) w e.store.nextActivation input)) ∧
      PV_W1_ClosedLeaves.Post320 C e H w input events :=
  ⟨rfl,PV_W1_ClosedLeaves.f320 C e H w input events pre⟩
#print axioms certified320

def model134 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (input : Data) :=
  PV_LIB.leafObserve (PV_W1_F134.call e.store (PV_THR2_OwnUniformResourceHandler.lift H) w e.store.nextActivation input)
def law134 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (input : Data)
    (out : PV_LIB.Observation (Answer Data) (Store Data × OWNER) E) : Prop :=
  out = model134 C e H w input

theorem certified134 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (input : Data) (events : List E)
    (pre : PV_W1_ClosedLeaves.Pre e w) :
    law134 C e H w input (PV_LIB.leafObserve (PV_W1_F134.call e.store (PV_THR2_OwnUniformResourceHandler.lift H) w e.store.nextActivation input)) ∧
      PV_W1_ClosedLeaves.Post134 C e H w input events :=
  ⟨rfl,PV_W1_ClosedLeaves.f134 C e H w input events pre⟩
#print axioms certified134

def model344 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (input : Data) :=
  PV_LIB.leafObserve (PV_W1_F344.call e.store (PV_THR2_OwnUniformResourceHandler.lift H) w e.store.nextActivation input)
def law344 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (input : Data)
    (out : PV_LIB.Observation (Answer Data) (Store Data × OWNER) E) : Prop :=
  out = model344 C e H w input

theorem certified344 {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (input : Data) (events : List E)
    (pre : PV_W1_ClosedLeaves.Pre e w) :
    law344 C e H w input (PV_LIB.leafObserve (PV_W1_F344.call e.store (PV_THR2_OwnUniformResourceHandler.lift H) w e.store.nextActivation input)) ∧
      PV_W1_ClosedLeaves.Post344 C e H w input events :=
  ⟨rfl,PV_W1_ClosedLeaves.f344 C e H w input events pre⟩
#print axioms certified344
end PV_LIB_PureLeaves
