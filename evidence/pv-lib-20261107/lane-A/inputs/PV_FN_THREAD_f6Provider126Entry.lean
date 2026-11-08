import PV_FN_THREAD_f126
import PV_FN_THREAD_f222_EntryOwned
import PV_FN_THREAD_f6DerefPre
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6Provider126Entry
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_FN_THREAD_f6Interfaces
abbrev Backend := PV_W1_OwnerNativeFrame.Backend

/-- Identical own activation, explicit store, saved return action, world,
event prefix and intrinsic stack; no caller cells are reconstructed. -/
def convert {E : Type} (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Backend E)
    (x : Entry E) : PV_FN_THREAD_f126_ReturnedStage.Input E :=
  {C := C,b := b,K := K,P := P,H := PV_THR2_OwnUniformResourceHandler.lift H,
   s := x.store,a := x.activation,dest := x.dest,parent := x.parent,
   parents := x.parents,wait := x.wait,ptr := .null,allocator := .null,
   w := x.world,es := x.events,stack := x.suspended}

/-- The converted provider entry is the identical consumer configuration.
No resolver or handler equality is inferred from this state equality. -/
theorem same_entry {E : Type} (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Backend E)
    (x : Entry E) (body : x.body = PV_THR2_F126.live) :
    PV_FN_THREAD_f126_Arbitrary.entry (convert C b K P H x) = entry x := by
  simp only [PV_FN_THREAD_f126_Arbitrary.entry,convert,entry,body]

theorem fields_read (B : Carrier OWNER Data) (v : Data) (is : List Nat) :
    fields B v is = readFields B is v := by
  induction is generalizing v with
  | nil => rfl
  | cons i is ih =>
    simp only [fields,readFields,Bind.bind]
    cases h : B.field v i <;> simp only [h,Option.bind_none,Option.bind_some,ih]

theorem at_read {E : Type} (M : Machine E) (s : Store Data) (p : Address) (v : Data)
    (owned : At M.carrier s p v) : readAddress M.carrier s p = some v := by
  rcases owned with ⟨root,cell,path⟩
  unfold readAddress
  rw [cell]
  change readFields M.carrier p.fields root = some v
  rw [← fields_read]
  exact path

/-- The corrected Arc shape, argument binding and ordinary entry invariant
supply ALL provider Pre clauses. No future read or successful reply is assumed. -/
theorem pre {E : Type} (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Backend E)
    (x : Entry E) (arcPlace p : Address)
    (valid : EntryValid x)
    (args : x.args = [PV_STX2_TypedReferences.reference arcPlace .null])
    (older : arcPlace.activation < x.activation)
    (root : At (PV_THR2_OwnInitExactReturnedCases.carrier C b) x.store arcPlace
      (PV_FN_THREAD_f222_EntryOwned.root p)) :
    PV_FN_THREAD_f126.Pre (convert C b K P H x) arcPlace p := by
  rcases valid with ⟨counter,parent,saved,action,request,owner,arguments⟩
  refine ⟨⟨?_,saved,action⟩,?_,older,?_,?_⟩
  · exact arguments 0 _ (by rw [args]; rfl)
  · change readAddress (PV_THR2_OwnInitExactReturnedCases.carrier C b) x.store arcPlace =
      some (PV_FN_THREAD_f222_EntryOwned.root p)
    exact at_read (⟨PV_THR2_OwnInitExactReturnedCases.carrier C b,K,P,
      PV_THR2_OwnUniformResourceHandler.lift H⟩ : Machine E) x.store arcPlace _ root
  · change x.activation < x.store.nextActivation
    omega
  · exact PV_W1_OwnerWellFormed.counter_mono x.world x.activation x.store.nextActivation
      owner (by omega)

/-- CLOSED126 is applied at ALL THREE actual f6 entries. This supplies its
exact reached-outcome Post on the provider's installed interpreter, not the
stronger all-prefix consumer FullPost. Interpreter identification and prefix
transport remain separate obligations; this theorem is not f6 closure. -/
theorem at_actual_sites {E : Type} (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Backend E)
    (site : PV_FN_THREAD_f6DerefInterfaces.Site) (t : Store Data) (a : Nat)
    (parents : List Frame) (saved : List LoopFrame) (w : OWNER) (es : List E)
    (stack : List Config) (p : Address)
    (live : a < t.nextActivation) (owner : OwnerWellFormed w t.nextActivation)
    (root : At (PV_THR2_OwnInitExactReturnedCases.carrier C b) t ⟨a,2,[0]⟩
      (PV_FN_THREAD_f222_EntryOwned.root p)) :
    let x := PV_FN_THREAD_f6DerefInterfaces.input site t a parents saved w es stack
    PV_FN_THREAD_f126.Post (convert C b K P H x) H ⟨a,2,[0]⟩ p := by
  apply PV_FN_THREAD_f126.contract
  apply pre C b K P H _ ⟨a,2,[0]⟩ p
  · exact PV_FN_THREAD_f6DerefInterfaces.valid site t a parents saved w es stack live owner
  · cases site <;> rfl
  · cases site <;> exact live
  · rcases root with ⟨value,cell,path⟩
    exact ⟨value,
      (PV_FN_THREAD_f6DerefPre.scope_cell site t a parents saved w es stack live).trans cell,path⟩

#print axioms same_entry
#print axioms fields_read
#print axioms at_read
#print axioms pre
#print axioms at_actual_sites
end PV_FN_THREAD_f6Provider126Entry
