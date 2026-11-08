import PV_LIB_A_GenericDropMachine
import PV_LIB_A_UnwindMatchCorrectness
import PV_LIB_A_TypedBindingFacts
set_option autoImplicit false
namespace PV_LIB_A_OptionDestruct157
open PV_STX2_Syntax PV_STX2_SliceSyntax PV_LIB_A_TypedDestruct

/-- Semantic sites, not invented emitted instructions. Rust Option has None=0
(no fields), Some=1 (field0:T); enum drop visits only the active variant.
This named library interpretation executes the payload destructor, rather than
replacing the whole Option drop with an arbitrary successful reply. -/
def site (n : Nat) : Site := ⟨157,n,.atom "documented Option drop glue"⟩

def receiver : Place := .project (.local 1) .deref
def payload : Place := .project receiver (.field 0)

/-- Keep T in the Destruct witness. Untracked means resolve by actual type,
never an unconditional noop. Resolution is delayed until Some is reached. -/
def payloadGlue (ty : Data) : Data := .object
  [("kind",.object [("Trait",.array [PV_LIB_A_TypedBindingFacts.untracked ty,.number 0])]),
   ("generics",encode ⟨[],[],[],[]⟩)]

def finish : List Node := [.leaf (.ret (site 3) (.local 0))]
def someBranch (ty : Data) : List Node :=
  [.leaf (.drop (site 2) payload (payloadGlue ty) false [.unwind (site 4)])] ++ finish

def branches (ty : Data) : List (List Nat × List Node) :=
  [([0],finish),([1],someBranch ty)]

/-- Named documented-semantics graph for the exact opaque function157.
Unknown/invalid enum tags stay interpreter gaps through matchAdt. The child
Drop keeps its ordinary failure/divergence/pending and cleanup delivery. -/
def PV_THR2_LibrarySemantics_OptionDestruct157 (ty : Data) : PV_STX2_SliceSyntax.Program :=
  ⟨157,.atom "documented generic Option destruction",.null,
    [.leaf (.aggregateMove (site 0) (.local 0) PV_LIB_A_GenericDropMachine.unitTag []),
     .matchAdt (site 1) receiver (branches ty) none]⟩

def instantiate (g : Generics) : Option PV_STX2_SliceSyntax.Program :=
  match g.types with
  | [ty] => if g.constants = [] ∧ g.traits = [] then
      some (PV_THR2_LibrarySemantics_OptionDestruct157 ty) else none
  | _ => none

theorem none_branch (ty : Data) :
    PV_STX2_SliceMachine.selectVariant 0 (branches ty) none = some finish := rfl

theorem some_branch (ty : Data) :
    PV_STX2_SliceMachine.selectVariant 1 (branches ty) none = some (someBranch ty) := rfl

theorem invalid_branch (ty : Data) (n : Nat) (h0 : n ≠ 0) (h1 : n ≠ 1) :
    PV_STX2_SliceMachine.selectVariant n (branches ty) none = none := by
  simp [PV_STX2_SliceMachine.selectVariant,branches,h0,h1]

theorem exact_type (ty : Data) (regions : List Data) :
    instantiate ⟨regions,[ty],[],[]⟩ =
      some (PV_THR2_LibrarySemantics_OptionDestruct157 ty) := rfl

#print axioms site
#print axioms receiver
#print axioms payload
#print axioms payloadGlue
#print axioms finish
#print axioms someBranch
#print axioms branches
#print axioms PV_THR2_LibrarySemantics_OptionDestruct157
#print axioms instantiate
#print axioms none_branch
#print axioms some_branch
#print axioms invalid_branch
#print axioms exact_type
end PV_LIB_A_OptionDestruct157
