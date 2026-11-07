import sys,pathlib,json
row=sys.argv[1];E=pathlib.Path('evidence/pv-lib-20261107/lane-SLICE')
order=['f21','f13','f6','f5','f8','f7','f9','f4','f2','f1','f0'];idx=json.loads((E/'SESSION4_CONTRACT_INDEX.json').read_text());prev=order[order.index(row)-1];assert prev in idx['statements']
ref='PV_STX2_TypedReferences.reference';tup='PV_STX2_SliceLoopCallback.indexTuple e.index.val'
args={
'f5':f'[column e.arrayAddress e.index.val,{tup}]',
'f8':f'[{ref} e.capture .null,{tup}]',
'f7':f'[wrapper e.arrayAddress e.index.val,{tup}]',
'f9':f'[{ref} e.buffer (.number 16),wrapper e.arrayAddress 0]',
'f4':'[wrapper e.arrayAddress 0]',
'f2':f'[{ref} e.arrayAddress .null]',
'f1':f'[{ref} e.arrayAddress .null]',
'f0':f'[{ref} e.foundationAddress .null]'}[row]
pre='ArrayPre m (start e) e'
mutable='[]';success='Clone r enc g e.toEntry (e.columns e.index) out v';extra=''
if row=='f8':
 pre='CapturePre m (start e) e true';mutable='[e.capture]'
 success='∃ value, v = wrappedValue value ∧ Clone r enc g e.toEntry (e.columns e.index) out value ∧\n      readAddress m.carrier (PV_STX2_ToVecCallCallerPost.statusStore out.status) e.capture =\n        some (wrapper e.arrayAddress (e.index.val+1))'
if row=='f7':success='∃ value, v = wrappedValue value ∧ Clone r enc g e.toEntry (e.columns e.index) out value'
if row=='f9':
 pre+=' ∧ e.buffer.activation < (start e).frame.activation ∧\n  ¬ inRoot e.buffer e.arrayAddress ∧\n  readAddress m.carrier (start e).store e.buffer =\n    some (.array (List.replicate 16 PV_STX2_SliceUninit.uninitValue))'
 mutable='[e.buffer]'
 extra='''/-- Initialized UNION slots, with the exact emitted nested constructors. -/
def initialized (v : Data) : Data :=
  PV_STX2_Aggregates.pack (PV_STX2_SliceClosureStores.kind PV_STX2_SliceF9.node110)
    [PV_STX2_Aggregates.pack (PV_STX2_SliceClosureStores.kind PV_STX2_SliceF9.node108)
      [PV_STX2_Aggregates.pack (PV_STX2_SliceClosureStores.kind PV_STX2_SliceF9.node107) [v]]]
'''
 success='''∃ values : Fin 16 → Data,
      v = PV_STX2_Aggregates.pack (PV_STX2_SliceClosureStores.kind PV_STX2_SliceF9.node146) [.null] ∧
      readAddress m.carrier (PV_STX2_ToVecCallCallerPost.statusStore out.status) e.buffer =
        some (.array (List.ofFn (fun i => initialized (values i)))) ∧
      ArrayClone r enc g e out (.array (List.ofFn values))'''
if row=='f4':success='∃ values, v = wrappedValue values ∧ ArrayClone r enc g e out values'
if row in ['f2','f1']:success='ArrayClone r enc g e out v'
entry='abbrev Entry := ArrayEntry';eparent='e.toEntry';earray='e'
if row=='f0':
 entry='''structure Entry extends ArrayEntry where
  foundationAddress : Address
  foundation : PV_STX2_Source7EntryOwned.Foundation'''
 eparent='e.toArrayEntry.toEntry';earray='e.toArrayEntry'
 pre='''ArrayPre m (start e) e.toArrayEntry ∧
  PV_STX2_Source7EntryReferenceValid.Source7EntryOwned e.owner e.foundation ∧
  e.arrayAddress = {e.foundationAddress with fields := e.foundationAddress.fields ++ [0]} ∧
  readAddress m.carrier (start e).store e.foundationAddress =
    some (PV_STX2_Aggregates.pack PV_STX2_AggregateKinds.source7Kind
      [.array (List.ofFn (fun i => vector (e.columns i).header))]) ∧
  (∀ i : Fin 16, (e.columns i).region.values =
    PV_STX2_Source7EntryOwned.values e.foundation ⟨i.val, by simpa using i.isLt⟩)'''
 success='∃ values, v = PV_STX2_Aggregates.pack PV_STX2_AggregateKinds.source7Kind [values] ∧\n      ArrayClone r enc g e.toArrayEntry out values'
# no string quoting can accidentally turn prime-bearing Lean names into Python delimiters
if row=='f0':pre=pre.replace("Source7EntryOwned e.owner", "Source7EntryOwned"+"'"*5+" e.owner")
s=f'''import PV_LIB_SLICE_Spec_{prev}
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SLICE_Spec_{row}
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OWNER PV_LIB_SLICE_Statements
{entry}
abbrev MachineSpec := PV_LIB_SLICE_Statements.MachineSpec
abbrev start (e : Entry) := PV_LIB_SLICE_Statements.start PV_STX2_Slice{row.upper()}.program
  {args} {eparent}

/-- Typed call-entry domain; no successful child, future read or callee Post. -/
def Pre (m : Machine) (e : Entry) : Prop := {pre}

{extra}/-- Exact first boundary on every arm, plus the row's source value clause. -/
def Post (r : Resources) (enc : Encode) (g : PV_OWN2_FreshAllocation.GrantedRegions)
    (m : Machine) (e : Entry) (impl : Outcome) : Prop :=
  PV_LIB_SLICE_Statements.Post r enc m (start e) {eparent} (sources {earray}) {mutable}
    (fun out v => {success}) impl

/-- A statement to be proved later, not an axiom or an instance. -/
def Contract (r : Resources) (enc : Encode) (g : PV_OWN2_FreshAllocation.GrantedRegions)
    (base : Carrier PV_STX_World.World Data) (ctrl : Control)
    (external : PV_W5_NoAllocShim.External) (backend : PV_W5_NativeFrame.Backend)
    (env : Environment) (impl : Machine → Entry → Outcome) : Prop :=
  ∀ m, MachineSpec m base ctrl external backend r enc env → ∀ e, Pre m e → Post r enc g m e (impl m e)
#print axioms Pre
#print axioms MachineSpec
#print axioms Post
#print axioms Contract
end PV_LIB_SLICE_Spec_{row}
'''
pathlib.Path('lean/PV_LIB_SLICE_Spec_'+row+'.lean').write_text(s)
