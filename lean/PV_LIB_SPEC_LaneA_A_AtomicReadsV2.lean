import PV_LIB_SPEC_LaneA_A_StoreAtomicV2
import PV_W1_NativeLeaves
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_AtomicReadsV2
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame
open PV_LIB_A_StorePrimitiveV2
/-- Atomic.v.UnsafeCell.value is read from the SAME source store as the
writer actions, including a source-backed BoxNew/Arc allocation. -/
def numeric (C : Carrier OWNER Data) (e : Entry) (w : OWNER) : Option Data := do
  match e.arguments with
  | [reference,_] =>
    let p ← atReference C e.store w reference [0,0]
    let .number n ← readAddress C e.store p | none
    pure (.number n)
  | _ => none

def boolean (C : Carrier OWNER Data) (e : Entry) (w : OWNER) : Option Data := do
  let value ← numeric C e w
  match value with
  | .number 0 => pure (.boolean false)
  | .number 1 => pure (.boolean true)
  | _ => none

def actual {E : Type} (H : Backend E) (e : Entry) (w : OWNER) : Reply OWNER E Data :=
  PV_THR2_OwnUniformResourceHandler.lift H
    (.child e.callee e.store.nextActivation e.arguments) w

/-- A value fact, never a Store-write premise. Native ordering/world/events
and every nonreturned answer remain the original full reply. Source/runtime
association is an explicit lower obligation, not claimed by this definition. -/
def ValueFact {E : Type} (read : Carrier OWNER Data → Entry → OWNER → Option Data)
    (C : Carrier OWNER Data) (e : Entry) (H : Backend E) (w : OWNER) : Prop :=
  ∀ result loaded, (actual H e w).answer = .returned (.ok result) →
    read C e w = some loaded → result = loaded

/-- ONE named documented-semantics fact per exact emitted function.
Rust core/sync/atomic.rs AtomicUsize/AtomicBool/AtomicU64::load (rust-src1.94.1
full source hash in session5/STD_SOURCES.json). These facts do NOT say that
an arbitrary backend satisfies them; actual-source binding remains open. -/
def PV_THR2_LibrarySemantics_AtomicLoad127 {E : Type}
    (C : Carrier OWNER Data) (e : Entry) (H : Backend E) (w : OWNER) : Prop :=
  PV_THR2_OffPath.functionId e.callee = some 127 → ValueFact numeric C e H w

def PV_THR2_LibrarySemantics_AtomicBoolLoad129 {E : Type}
    (C : Carrier OWNER Data) (e : Entry) (H : Backend E) (w : OWNER) : Prop :=
  PV_THR2_OffPath.functionId e.callee = some 129 → ValueFact boolean C e H w

def PV_THR2_LibrarySemantics_AtomicLoad528 {E : Type}
    (C : Carrier OWNER Data) (e : Entry) (H : Backend E) (w : OWNER) : Prop :=
  PV_THR2_OffPath.functionId e.callee = some 528 → ValueFact numeric C e H w

/-- Normalization is equality of the ACTUAL full reply once its named value
fact holds. No outcome is restricted; malformed/unbound source representations
retain the original reply and earn no source-adequacy credit. -/
def modelReply {E : Type} (read : Carrier OWNER Data → Entry → OWNER → Option Data)
    (C : Carrier OWNER Data) (e : Entry) (w : OWNER) (r : Reply OWNER E Data) : Reply OWNER E Data :=
  match r.answer with
  | .returned (.ok _) => match read C e w with
    | some value => {r with answer := .returned (.ok value)}
    | none => r
  | _ => r

theorem reply_exact {E : Type} (read : Carrier OWNER Data → Entry → OWNER → Option Data)
    (C : Carrier OWNER Data) (e : Entry) (H : Backend E) (w : OWNER)
    (fact : ValueFact read C e H w) :
    actual H e w = modelReply read C e w (actual H e w) := by
  generalize eq : actual H e w = r
  have facts : ∀ result loaded, r.answer = .returned (.ok result) →
      read C e w = some loaded → result = loaded := by
    intro result loaded answer source
    exact fact result loaded (eq.symm ▸ answer) source
  rcases r with ⟨answer,world,events⟩
  cases answer with
  | pending => rfl
  | fault f => rfl
  | returned result =>
    cases result with
    | fail err => rfl
    | div => rfl
    | ok value =>
      cases source : read C e w with
      | none => simp only [modelReply,source]
      | some loaded =>
        have same := facts value loaded rfl source
        subst value
        simp only [modelReply,source]

theorem at127 {E : Type} (C : Carrier OWNER Data) (e : Entry) (H : Backend E) (w : OWNER)
    (fact : PV_THR2_LibrarySemantics_AtomicLoad127 C e H w)
    (function : PV_THR2_OffPath.functionId e.callee = some 127) :
    actual H e w = modelReply numeric C e w (actual H e w) := reply_exact numeric C e H w (fact function)

theorem at129 {E : Type} (C : Carrier OWNER Data) (e : Entry) (H : Backend E) (w : OWNER)
    (fact : PV_THR2_LibrarySemantics_AtomicBoolLoad129 C e H w)
    (function : PV_THR2_OffPath.functionId e.callee = some 129) :
    actual H e w = modelReply boolean C e w (actual H e w) := reply_exact boolean C e H w (fact function)

theorem at528 {E : Type} (C : Carrier OWNER Data) (e : Entry) (H : Backend E) (w : OWNER)
    (fact : PV_THR2_LibrarySemantics_AtomicLoad528 C e H w)
    (function : PV_THR2_OffPath.functionId e.callee = some 528) :
    actual H e w = modelReply numeric C e w (actual H e w) := reply_exact numeric C e H w (fact function)

#print axioms PV_THR2_LibrarySemantics_AtomicLoad127
#print axioms PV_THR2_LibrarySemantics_AtomicBoolLoad129
#print axioms PV_THR2_LibrarySemantics_AtomicLoad528
#print axioms reply_exact
#print axioms at127
#print axioms at129
#print axioms at528
end PV_LIB_A_AtomicReadsV2
