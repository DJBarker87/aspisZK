import json,pathlib,subprocess
L=pathlib.Path('evidence/pv-lib-20261107/lane-SPEC')
d=json.loads(subprocess.check_output(['git','show','5e397cb3878:evidence/pv-lib-20261107/DEPENDENCIES.json']))
rows=[r for r in d['rows'] if r['id'].startswith('thread:') and r['source'].get('syntax')]
imports='\n'.join('import '+pathlib.Path(r['source']['syntax']).stem for r in rows)
cases='\n'.join('  | '+r['id'].split('f')[-1]+' => some '+pathlib.Path(r['source']['syntax']).stem+'.live' for r in rows)
text='''import PV_LIB_SPEC_F166Whole
'''+imports+'''
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Full
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_LIB_SPEC_D984 PV_LIB_SPEC_Row
/-- Every emitted thread BODY in the frozen dependency closure, including
CLOSED124/126 and setter207. Native leaves have no invented body. This table
is OUTSIDE the old prefix resolvers: their deliberate124/126 exclusions must
not turn a whole reference into an arbitrary full-reply prefix. -/
def body : Nat → Option PV_STX2_SliceSyntax.Program
'''+cases+'''
  | _ => none
/-- Complete emitted-body interpretation, retaining source-derived trait
resolution and the intrinsic318 callback interception. There is no fallback
Ops dictionary that can supply an arbitrary BODY result. Native leaf replies
remain the explicit environment and named documented-semantics obligations. -/
def programs (fn : Data) : Option PV_STX2_SliceSyntax.Program :=
  match PV_THR2_OffPath.functionId fn with
  | some id => body id
  | none => PV_LIB_SPEC_D984.programs (fun _ => none) fn

def source (table : FullStoreActionTable) (r : Runtime) : Machine :=
  ⟨r.carrier,r.control,programs,r.native,r.resources,r.encode,table⟩
/-- Arbitrary candidate machine with named source carrier/control and the
FULL emitted table. Leaf interpretation/resource association is a separate
named adequacy target, not a future-store, read or successful-call premise. -/
def MachineSpec (table : FullStoreActionTable) (r : Runtime) (m : Machine) : Prop :=
  m.carrier = r.carrier ∧ m.control = r.control ∧ m.programs = programs ∧
  m.handler = r.native ∧ @m.resources = @r.resources ∧ @m.encode = @r.encode ∧
  m.storeActions = table

def Post (table : FullStoreActionTable) (r : Runtime)
    (body : PV_STX2_SliceSyntax.Program) (i : Input) (candidate : Nat → State) : Prop :=
  Behavior (source table r) (entry body i) candidate ∧
  ∀ k, (∀ j, j < k → ¬ Boundary (source table r) (entry body i) candidate j) →
    match (candidate k).current.status with
    | .fault .abort _ => True
    | _ => PV_LIB_SPEC_ThreadRow.Frame r i (candidate k)

/-- Source association is a target, never a new endpoint premise. It must
bind source operations, full replies/resources, typed representations and
compiler/translator/binary facts at actual source arguments. -/
def SourceAdequacy (table : FullStoreActionTable) (r : Runtime)
    (body : PV_STX2_SliceSyntax.Program) (arity : Nat)
    (actual : Input → Nat → State) : Prop :=
  ∀ i, PV_LIB_SPEC_Row.Pre body arity r i → Post table r body i (actual i)

#print axioms body
#print axioms programs
#print axioms source
#print axioms MachineSpec
#print axioms Post
#print axioms SourceAdequacy
end PV_LIB_SPEC_Full

namespace PV_LIB_SPEC_F361Full
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_LIB_SPEC_D984 PV_LIB_SPEC_Row
abbrev Input := PV_FN_THREAD_f361.Input
abbrev Representation := PV_LIB_SPEC_F361Whole.Representation
/-- Canonical named provider carrier (with operator/binary Box casts), framed
native lift and resource channels; arbitrary old sourceStep/changes are unused. -/
def runtime (x : Input) : Runtime :=
  ⟨PV_FN_THREAD_f361.base x,x.K,x.P,PV_FN_THREAD_f361.handler x,x.resources,x.encode⟩
def source (table : FullStoreActionTable) (x : Input) : Machine :=
  PV_LIB_SPEC_Full.source table (runtime x)
def MachineSpec (table : FullStoreActionTable) (x : Input) (m : Machine) : Prop :=
  PV_LIB_SPEC_Full.MachineSpec table (runtime x) m
abbrev Pre := PV_LIB_SPEC_F361Whole.Pre
/-- Full function, not OwnInit14756. Exact Thread/Packet/CString/Arc/Box fields,
full spawn success/Err/cleanup and all earlier stops come from the complete
emitted reference. The actual full table supplies Arc strong-count writes. -/
def Post (table : FullStoreActionTable) (x : Input) (candidate : Nat → State) : Prop :=
  Behavior (source table x) (PV_FN_THREAD_f361.entry x) candidate ∧
  ∀ k, First (source table x) (PV_FN_THREAD_f361.entry x) candidate k →
    match (candidate k).current.status with
    | .fault .abort _ => True
    | _ => PV_FN_THREAD_f361.Frame x (candidate k) ∧ Numbered (candidate k)
def Contract (table : FullStoreActionTable) (R : Representation)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m x, MachineSpec table x m → Pre R x → Post table x (implementation m x)
/-- Literal old package statement is preserved; no implication to the whole
corrected reference is silently asserted. -/
abbrev PackagePre := PV_FN_THREAD_f361.Pre
abbrev PackagePost := PV_FN_THREAD_f361.Post

def Comparison (table : FullStoreActionTable) (R : Representation)
    (implementation : Machine → Input → Nat → State) : Prop :=
  (∀ x, Pre R x ↔ PackagePre x ∧
    PV_FN_THREAD_f361NameEntryValidity.EntryName R x ∧
    PV_FN_THREAD_f361ScopeEntryValidity.Shape x.scope ∧
    PV_LIB_SPEC_F361Entry.Numbered x ∧ RegisteredValidity x.w) ∧
  Contract table R implementation
#print axioms runtime
#print axioms source
#print axioms MachineSpec
#print axioms Pre
#print axioms Post
#print axioms Contract
#print axioms PackagePre
#print axioms PackagePost
#print axioms Comparison
end PV_LIB_SPEC_F361Full
'''
p=pathlib.Path('lean/PV_LIB_SPEC_F361Full.lean');p.write_text(text)
(L/'SESSION5_BODY_TABLE.json').write_text(json.dumps({'freeze':'5e397cb3878','rows':rows,'reason':'whole reference cannot use deliberate BODY exclusions from package prefix tables'},indent=2)+'\n')
