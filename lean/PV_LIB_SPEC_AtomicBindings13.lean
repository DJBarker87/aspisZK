import PV_LIB_SPEC_NativeMemory12
import PV_LIB_SPEC_AtomicRecheck12
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_AtomicBindings13
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen

/-- Atomic loads use the actual request arguments and current source store.
No reference, value or successful decoder is supplied by a caller. The
retained lane-A numeric/boolean models select precisely [0,0]. -/
def entry (c : Config) (fn : Data) (args : List Data) : PV_W1_LeafBoundary.Entry :=
  ⟨c.store,c.frame.activation,[],[],[],fn,args,0,[]⟩

def load (p : Parameters) (c : Config) (w : OWNER)
    (fn : Data) (args : List Data) : Option Data :=
  match PV_THR2_OffPath.functionId fn with
  | some 127 | some 528 =>
    PV_LIB_A_AtomicReadsV2.numeric (runtime p).carrier (entry c fn args) w
  | some 129 =>
    PV_LIB_A_AtomicReadsV2.boolean (runtime p).carrier (entry c fn args) w
  | _ => none

/-- The full backend answer selects the outcome. Only a returned success is
bound to its source value. Malformed successful loads explicitly fail
interpretation rather than retain an unrelated success marker. -/
def reply (p : Parameters) (c : Config) (w : OWNER) (fn : Data) (args : List Data)
    (r : Reply OWNER Event Data) : Option (Reply OWNER Event Data) :=
  match r.answer with
  | .returned (.ok _) => do
    let value ← load p c w fn args
    pure {r with answer := .returned (.ok value)}
  | _ => some r

theorem other (p : Parameters) (c : Config) (w : OWNER) (fn : Data) (args : List Data)
    (r : Reply OWNER Event Data) (h : ∀ v, r.answer ≠ .returned (.ok v)) :
    reply p c w fn args r = some r := by
  cases a : r.answer with
  | pending => simp only [reply,a]
  | fault f => simp only [reply,a]
  | returned result => cases result with
    | ok v => exact False.elim (h v a)
    | fail e => simp only [reply,a]
    | div => simp only [reply,a]

theorem effects (p : Parameters) (c : Config) (w : OWNER) (fn : Data) (args : List Data)
    (r out : Reply OWNER Event Data) (h : reply p c w fn args r = some out) :
    out.world = r.world ∧ out.events = r.events := by
  unfold reply at h
  split at h
  · cases source : load p c w fn args with
    | none => simp only [source,Option.bind_none] at h; cases h
    | some value => simp only [source,Option.bind_some,Option.pure_def] at h; cases h; exact ⟨rfl,rfl⟩
  · cases h; exact ⟨rfl,rfl⟩

/-- The actual F6 numeric-u8 panic load now gets its source bool on both
constructor values. This is a local request check; no original reachability. -/
def config (b : Bool) : Config :=
  ⟨{activation := 7,remaining := []},[],PV_LIB_SPEC_AtomicRecheck12.store b⟩
def args : List Data := [PV_STX2_TypedReferences.reference ⟨7,50,[]⟩ .null,.null]

theorem constructor_load (b : Bool) :
    load PV_LIB_SPEC_ConcreteEntry.parameters (config b)
      PV_LIB_SPEC_ConcreteCaptures.state PV_LIB_SPEC_AtomicRecheck12.loadFn args =
      some (.boolean b) := by
  cases b <;> rfl

#print axioms entry
#print axioms load
#print axioms reply
#print axioms other
#print axioms effects
#print axioms config
#print axioms args
#print axioms constructor_load
end PV_LIB_SPEC_AtomicBindings13
