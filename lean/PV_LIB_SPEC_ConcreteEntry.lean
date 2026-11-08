import PV_LIB_SPEC_ConcreteCaptures
import PV_LIB_SPEC_ResourceHistory
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ConcreteEntry
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen

/-- Concrete primitive data interpretation. The frozen runtime installs its
source scalar/aggregate/typed-reference operators on this base by name. -/
def primitives : Carrier OWNER Data :=
  {global := fun _ _ => none,constant := some,dereference := fun _ _ => none
   field := fun _ _ => none,replaceField := fun _ _ _ => none,metadata := fun _ => none
   reference := PV_STX2_TypedReferences.reference
   aggregate := fun kind args => some (PV_THR2_KeyValues.pack kind args)
   unary := fun _ value => some value,binary := fun _ _ _ => none
   nullary := fun _ _ => none,truth := fun v => match v with | .boolean b => some b | _ => none
   matchesKey := fun _ _ => false}

def resources : Resources := fun _ w => ⟨.pending,w.allocator,w.errno⟩
def environment : Environment :=
  {allocation := fun req => resources req.operation req.before
   reservation := fun req => resources req.operation req.before
   native := fun _ w => ⟨.pending,w,[]⟩}
def parameters : Parameters :=
  ⟨primitives,⟨fun _ => none,fun _ _ _ => none⟩,false,resources,
    (fun _ _ => []),PV_LIB_SPEC_ConcreteCaptures.zero,⟨0,by decide⟩,environment⟩

def store : Store Data :=
  ⟨fun p => if p = ⟨1,1,[]⟩ then some (.number 1)
    else if p = ⟨1,2,[]⟩ then some PV_LIB_SPEC_ConcreteCaptures.closure
    else if p = ⟨0,12,[]⟩ then some .null else none,2⟩
def input : OwnInit.Input := ⟨store,1,1,PV_LIB_SPEC_ConcreteCaptures.closure,PV_LIB_SPEC_ConcreteCaptures.state,[]⟩

theorem fresh : PV_EVHB_SourceLifetimes.Fresh PV_LIB_SPEC_ConcreteCaptures.state := by
  intro p id selected
  simp only [PV_LIB_SPEC_ConcreteCaptures.state] at selected ⊢
  split at selected
  · cases selected; decide
  · split at selected
    · cases selected; decide
    · split at selected
      · cases selected; decide
      · split at selected
        · cases selected; decide
        · cases selected

theorem owner (counter : Nat) (positive : 0 < counter) :
    PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed PV_LIB_SPEC_ConcreteCaptures.state counter := by
  refine ⟨fresh,?_⟩
  intro p id selected
  simp only [PV_LIB_SPEC_ConcreteCaptures.state] at selected
  split at selected
  · rename_i equal; subst p; exact positive
  · split at selected
    · rename_i equal; subst p; exact positive
    · split at selected
      · rename_i equal; subst p; exact positive
      · split at selected
        · rename_i equal; subst p; exact positive
        · cases selected

theorem validity : RegisteredValidity PV_LIB_SPEC_ConcreteCaptures.state := by
  intro p id h selected found
  simp only [PV_LIB_SPEC_ConcreteCaptures.state] at selected
  split at selected
  · cases selected
    have eq : h = PV_LIB_SPEC_ConcreteCaptures.runHeader := by simpa [PV_EVHB_RawVecOwner.lookup,PV_LIB_SPEC_ConcreteCaptures.state] using found.symm
    subst h
    exact ⟨by decide,by decide,by decide,by decide⟩
  · split at selected
    · cases selected
      have eq : h = PV_LIB_SPEC_ConcreteCaptures.nHeader := by simpa [PV_EVHB_RawVecOwner.lookup,PV_LIB_SPEC_ConcreteCaptures.state] using found.symm
      subst h
      exact ⟨by decide,by decide,by decide,by decide⟩
    · split at selected
      · cases selected
        have eq : h = PV_LIB_SPEC_ConcreteCaptures.fHeader := by simpa [PV_EVHB_RawVecOwner.lookup,PV_LIB_SPEC_ConcreteCaptures.state] using found.symm
        subst h
        exact ⟨by decide,by decide,by decide,by decide⟩
      · split at selected
        · cases selected
          have eq : h = PV_LIB_SPEC_ConcreteCaptures.taskHeader := by simpa [PV_EVHB_RawVecOwner.lookup,PV_LIB_SPEC_ConcreteCaptures.state] using found.symm
          subst h
          exact ⟨by decide,by decide,by decide,by decide⟩
        · cases selected

def reference : Data := PV_STX2_TypedReferences.reference ⟨0,12,[]⟩ .null
inductive Value : Data → Prop where
  | count : Value (.number 1)
  | closure : Value PV_LIB_SPEC_ConcreteCaptures.closure
  | reference : Value reference
  | unit : Value .null

theorem fields (v child : Data) (n : Nat) (valid : Value v)
    (field : (runtime parameters).carrier.field v n = some child) : Value child := by
  cases valid with
  | count => cases field
  | closure =>
    cases n with
    | zero => cases field; exact Value.reference
    | succ n => cases field
  | reference => cases field
  | unit => cases field

theorem dereference (v : Data) (p : Address) (valid : Value v)
    (address : (runtime parameters).carrier.dereference input.world v = some p) :
    p = ⟨0,12,[]⟩ := by
  cases valid with
  | count => cases address
  | closure => cases address
  | reference => exact (Option.some.inj address).symm
  | unit => cases address

theorem reachable (v : Data)
    (reached : PV_LIB_SPEC_Row.Reachable (runtime parameters)
      (PV_LIB_SPEC_F0Full.referenceInput input) v) : Value v := by
  induction reached with
  | argument member =>
    change _ ∈ [.number 1,PV_LIB_SPEC_ConcreteCaptures.closure] at member
    rcases List.mem_cons.mp member with rfl | member
    · exact Value.count
    · rcases List.mem_singleton.mp member with rfl
      exact Value.closure
  | field n _ selected ih => exact fields _ _ n ih selected
  | pointee _ address read ih =>
    have eq := dereference _ _ ih address
    subst eq
    change some Data.null = some _ at read
    cases read
    exact Value.unit

theorem references : References (runtime parameters)
    (PV_LIB_SPEC_F0Full.referenceInput input) := by
  intro v p reached address
  have eq := dereference v p (reachable v reached) address
  subst p
  exact ⟨.null,rfl⟩

theorem numbered : Numbered (PV_LIB_SPEC_F0Full.rootEntry input) := by
  constructor
  · intro c eq
    cases eq
    exact ⟨by decide,True.intro,True.intro⟩
  · intro c member; cases member

/-- The complete CURRENT frozen OwnInit entry conjunction, now on ONE concrete
store, nonempty capture OWNER, runtime, environment and positive n. This is
not the old entry-only capture theorem, nor a universal row contract proof. -/
theorem pre : OwnInit.Pre parameters input := by
  refine ⟨rfl,rfl,owner 2 (by decide),owner 1 (by decide),validity,numbered,references,?_⟩
  exact ⟨Unit,Unit,PV_LIB_SPEC_ConcreteCaptures.captures,rfl,PV_LIB_SPEC_ConcreteCaptures.entry_nonempty⟩

theorem machine (table : FullStoreActionTable) :
    MachineSpec table parameters (source table parameters) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem joint (table : FullStoreActionTable) :
    OwnInit.Pre parameters input ∧ 0 < input.n ∧
      MachineSpec table parameters (source table parameters) :=
  ⟨pre,by decide,machine table⟩

#print axioms primitives
#print axioms resources
#print axioms environment
#print axioms parameters
#print axioms store
#print axioms input
#print axioms fresh
#print axioms owner
#print axioms validity
#print axioms reference
#print axioms Value
#print axioms fields
#print axioms dereference
#print axioms reachable
#print axioms references
#print axioms numbered
#print axioms pre
#print axioms machine
#print axioms joint
end PV_LIB_SPEC_ConcreteEntry
