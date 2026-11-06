#!/usr/bin/env python3
"""Draft contracts and conservative evidence assessments; never generates proofs."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
EVID = ROOT / 'evidence/pv-ledger-20261108'
DRAFTS = {
'slice': {
0: ('Foundation reference; Source7EntryOwned\'\'\' including registry linkage and OwnerWellFormed', 'Return the cloned Foundation: sixteen owned columns, each with the entry column length and bytes, with disjoint fresh destination regions and entry regions preserved.'),
1: ('Reference to the sixteen-Vec column array with per-column ownership', 'Return an array of sixteen cloned Vecs in source column order; preserve the original array and all input bytes.'),
2: ('Reference to the sixteen-Vec array and its registered column descriptors', 'Use from_fn and the source clone closure to build sixteen destination Vecs in order, preserving the input array.'),
4: ('Generator and output element layout; public array length sixteen', 'Return the complete initialized array if all generator calls continue; otherwise retain the first residual, its initialized prefix and the source cleanup effects.'),
5: ('Clone closure capture and the source column index', 'Forward the actual capture and index to call_mut and return its cloned Vec.'),
6: ('Capture referencing the source array and an in-range column index', 'Derive the indexed column reference from the capture, clone that Vec, and return it without changing the source column.'),
7: ('NeverShortCircuit wrapper capture and source index', 'Invoke the inner generator and wrap its value in NeverShortCircuit, preserving its effects.'),
8: ('Mutable wrapper capture with the source generator and index', 'Invoke the source generator with the actual index and return the NeverShortCircuit-wrapped value.'),
9: ('Uninitialized buffer of sixteen elements, generator, initialized-prefix invariant at call entry', 'Run the sixteen-column loop; maintain initialized-prefix ownership, advance one slot per successful call, return the complete initialized buffer or the exact first residual/cleanup branch.'),
11: ('Actual residual value of the emitted Try instantiation', 'Return the emitted residual conversion; preserve all caller memory.'),
12: ('Actual completed array value of the emitted Try instantiation', 'Return the emitted successful output conversion; preserve all caller memory.'),
13: ('Reference to a Vec descriptor with valid registered source pointer/length and typed M31 bytes', 'Return a fresh owned Vec with the same length and bytes as the entry Vec, retaining its allocator representation; preserve source descriptor and bytes.'),
15: ('Actual NeverShortCircuit value', 'Return the Continue discriminant containing its inner value with no memory mutation.'),
21: ('Source pointer, public length n, allocator; readable registered M31 range, OwnerWellFormed, typed length/layout constraints', 'Return a fresh owned Vec of length n containing the entry source bytes. Include zero length, allocation/layout error and null branches. Execute copy and set_len, and return to the saved f13 caller with the explicit final store.'),
23: ('Element layout and the source uninitialized representation', 'Return the uninitialized storage representation without reading uninitialized bytes or changing caller cells.'),
31: ('Requested capacity, allocator and Layout arguments with typed sizes', 'Return the RawVec representation for the requested capacity, including zero capacity; preserve the returned allocation/header identity and exact errors from try_allocate_in.'),
32: ('Source, destination, byte count and emitted UB-check configuration', 'Return unit when the copy precondition check passes; otherwise take the exact emitted abort branch. This check itself does not perform the byte copy.'),
33: ('Vec capacity and requested new length; pinned UB-check configuration', 'Return unit if the set_len precondition check passes, otherwise the exact emitted abort; do not change Vec bytes in the check.'),
35: ('Requested capacity, element Layout, allocator and allocation mode', 'Return the actual allocation Result with correct capacity/layout/header on success; retain zero size, overflow, allocator error, null and failure branches.'),
47: ('Allocator and requested Layout', 'Forward the uninitialized allocation request to alloc_impl_runtime and return its exact allocation Result and world effects.'),
48: ('Allocator and requested Layout', 'Forward the zeroed allocation request to alloc_impl_runtime; on success return a valid zeroed region, retaining every allocation failure.'),
59: ('Layout size/alignment, allocator and zeroed flag', 'Issue the source-selected allocation/shim requests in order; return the pointer/length Result, with zero-size representation and null failure handled exactly. Memory outside the granted region is preserved by the named allocation byte frame.'),
},
'thread': {
0: ('n, worker function/captures; OrderedFamiliesEntryOwned\' with registry/representation linkage', 'Return the ordered family Vec on completion, preserving captures; all scope, worker, allocation and OS resource outcomes remain observable in source order.'),
1: ('n, f and worker flag; typed capture regions and public iteration bounds', 'Follow the source worker/sequential branch, scope, spawn and join order and return ordered results; preserve entry capture ownership with exact handle/worker effects.'),
2: ('Source TLS key and capture environment', 'Return the actual worker flag read via the source TLS with callback; retain each TLS failure and preserve unrelated cells.'),
5: ('Source TLS key and guard capture', 'Set the active worker flag through the actual callback and return the guard, retaining TLS failure and its declared write.'),
6: ('Scope callback and its captures, registered entry references', 'Construct the actual Scope, execute catch_unwind and callback, finish scope completion and return its result; retain panic/abort and resource branches. Both Arc instances have explicit final stores.'),
17: ('LocalKey reference and FnOnce callback argument', 'Invoke try_with with actual captures, returning its value or taking the source access-error panic branch.'),
170: ('LocalKey reference and callback with its recorded captures', 'Select the source initializer token, consume its arbitrary reply, and invoke the actual callback on the returned TLS reference; return the Result and retain every failure or missing-representation branch.'),
124: ('Value T, typed ArcInner layout, fresh activation and caller continuation', 'Return Arc<T> whose pointer denotes the newly initialized ArcInner with strong=1, weak=1 and data equal to entry T. Use actual BoxNew and 217/312/313 replies under their named semantics, and retain the full explicit final store and all allocation/counter failure branches.'),
125: ('Actual callback and capture arguments to panic::catch_unwind', 'Return catch_unwind Result after running std::panicking::catch_unwind on those arguments; preserve the exact callback effects and pinned panic strategy.'),
126: ('Reference to a valid three-field Arc<T> representation, with registered allocation root; no assumed future read', 'Return a reference to the data field [2] of that actual ArcInner allocation, world and pointee unchanged. Derive the address through inner and NonNull::as_ref.'),
15: ('Actual scope reference and captured n/f, with entry-owned capture registration', 'Construct handles, iterate next93, spawn f166 on each Some index with source-derived captures, push handles and join in source order; None exits without a ThreadInit allocation, preserving failures and explicit stores.'),
164: ('Allocator/layout for handles Vec constructor', 'Return the outermost new-RawVec child result wrapped as the handles Vec, retaining arbitrary full reply and effects; do not assume an empty-value identity for the scoped OwnInit prefix.'),
166: ('Scope reference and actual move closure with registered captures', 'Construct Builder, invoke spawn_scoped and consume its Result; on success return ScopedJoinHandle with the actual captures, preserving exact OS/failure effects.'),
208: ('Source scope closure environment and scope reference', 'Invoke the user closure f15 with the actual scope reference and captures and return its value/effects.'),
216: ('Box<T,A> argument with allocated pointee and allocator', 'Return a mutable reference to the same pointee by into_raw_with_allocator and forget; preserve initialized pointee bytes and record ownership transfer, with exact child outcomes.'),
218: ('NonNull<ArcInner<T>> and source allocator representation', 'Return Arc<T> constructed from that NonNull and allocator through from_inner_in; do not manufacture a new allocation or change pointee bytes.'),
219: ('catch_unwind callback, data and result storage', 'Invoke the preserved higher-order intrinsic once at its actual arguments and retain the callback result/explicit final store; preserve abort under pinned panic strategy.'),
220: ('AssertUnwindSafe wrapper and callback arguments', 'Unwrap the actual wrapper and invoke f208 at the source arguments; return its reply and effects.'),
222: ('Reference to valid Arc<T> representation', 'Return reference to its actual ArcInner via opaque320 documented semantics; no store/pointee writes.'),
270: ('Builder, scope reference and closure captures', 'Clone scope bookkeeping and invoke spawn_unchecked with the actual closure and scope; return the actual scoped handle/Result with exact OS resource branches.'),
315: ('NonNull inner pointer and allocator value', 'Return emitted Arc aggregate containing the same pointer, PhantomData and allocator; no heap writes.'),
316: ('Actual data pointer and callback/result storage for do_call', 'Read the actual capture, invoke 220 at those arguments, and write the result to the argument-reachable result cell. Carry that caller-cell delta explicitly through return.'),
361: ('Builder, closure/captures and scope; entry-owned registered regions and typed representations', 'Construct Thread, Packet Arc and worker closure; register and allocate the ThreadInit box at 14756 with its actual fields from source stores. Retain all later return/spawn effects and all failure branches; OwnInit is a marked intermediate milestone, not the function return.'),
443: ('Owned Box and source allocator representation', 'Return raw pointer to that same Box allocation via source ManuallyDrop operations, without changing its pointee; record ownership transfer.'),
458: ('Valid raw Box pointer and allocator provenance supplied by actual arguments', 'Reconstruct Box from the same pointer through from_raw_in; preserve pointee bytes and transfer ownership without allocating.'),
537: ('Valid raw pointer and allocator with the emitted Box layout', 'Construct the Box using the actual Unique::new_unchecked child and allocator; preserve allocation bytes and every full child outcome.'),
'F0->f361@14756': ('OrderedFamiliesEntryOwned\', public n and actual captures; Some iteration case of next93', 'Compose the original entry to OwnInit at ThreadInit: registered allocation and stored source-derived captures on the spawning branch; None iteration exits with no box, and each fault/abort/divergence/pending remains at its exact source site/world/events.'),
}}

FACTS = {
('thread',134): 'PV_THR2_IntrinsicSemantics_ManuallyDropNew134',
('thread',217): 'PV_THR2_IntrinsicSemantics_NonNullFrom217',
('thread',312): 'PV_THR2_IntrinsicSemantics_BoxIntoRawWithAllocator312',
('thread',313): 'PV_THR2_IntrinsicSemantics_MemForget313',
('thread',318): 'PV_THR2_IntrinsicSemantics_catch_unwind',
('thread',320): 'PV_THR2_IntrinsicSemantics_NonNullAsRef',
('thread',344): 'PV_THR2_IntrinsicSemantics_ManuallyDropDerefMut344',
('thread',214): 'PV_THR2_OperatorSemantics_214',
('slice',63): 'PV_STX2_IntrinsicSemantics_NoAllocShim',
('slice','builtin:CopyNonOverlapping'): 'PV_STX2_IntrinsicSemantics_CopyNonOverlapping',
('slice','builtin:{"PtrFromParts":"Mut"}'): 'PV_STX2_IntrinsicSemantics_PtrFromPartsMut',
}
# Local results only: original-entry achievements are contextual evidence below.
CANDIDATES = {
('thread',124): [('PV_THR2_Packet124WholeReturn','run'), ('PV_THR2_Packet124LocalReturn','run')],
('thread',126): [('PV_THR2_Packet126WholeReturn','run')],
('thread',216): [('PV_THR2_Packet216ToCallerLocal','run')],
('thread',218): [('PV_THR2_Packet218SourceReturn','run')],
('thread',315): [('PV_THR2_Packet315SourceReturn','run')],
('thread',222): [('PV_THR2_Packet222SemanticReturn','run')],
('thread',361): [('PV_THR2_Source361Prologue',None), ('PV_THR2_PacketJoinedMetadataRun',None), ('PV_THR2_PacketJoinedBoxRun',None)],
('slice',21): [('PV_STX2_ToVecCallWrappers','source262'), ('PV_STX2_Source7QUniformReturn','PV_STX2_Source7QUniformReturn'), ('PV_STX2_Source7QColumnViewReturn','returned')],
('slice',31): [('PV_STX2_ToVecF31Return','source13')],
('slice',35): [('PV_STX2_ToVecConstructorReturn','source25')],
}

def get(rev,path):
    return subprocess.check_output(['git','show',f'{rev}:{path}'],cwd=ROOT).decode()

def main():
    ledger = json.loads((EVID/'enumeration.json').read_text())
    ledger['contract_convention'] = {
      'state': 'Draft mathematical interfaces, not Lean declarations and not proofs. C = (Pre, Post); all row-specific clauses below are conjuncts of the common call-entry/return convention.',
      'parameters': ['actual arguments args', 'arbitrary lower caller stack kappa', 'entry store sigma', 'entry OWNER state s', 'entry world w', 'argument-reachable caller cells R(args,sigma,s)', 'prior event prefix'],
      'entry': 'Enter this exact emitted body with args installed in its own fresh activation; kappa is arbitrary and read only to return. Pre contains only entry well-formedness, typing, ownership/layout and source domain conditions; it contains no callee contract, future read, success or desired result.',
      'reply_branches': {
        'returned': 'Return the actual answer, explicit final store, OWNER state, world and event suffix; establish the row-specific value/ownership relation and writes to R(args,sigma,s). Restore the actual saved caller continuation and return destination.',
        'failure': 'Keep the exact error/fault/panic/abort and the world, events and store at the failing site. Apply the named pinned panic strategy, retaining emitted cleanup syntax.',
        'divergence': 'Preserve divergence and its observable prefixes; do not claim a finite return.',
        'pending': 'Preserve the running configuration waiting at the actual child request, with exact world/events; do not call it a non-running terminal.'},
      'frame': 'The explicit final store agrees with sigma on every pre-existing caller cell outside R(args,sigma,s) and the return destination. Writes to fresh local activations and newly allocated owned regions are tracked separately. Old heap bytes/OWNER bindings outside the argument-reachable modified region are preserved by named memory/export frames. The lower stack and prior events are preserved. Each world/OS child may change only its declared footprint; its declaration is an open named obligation where not yet supplied. No unconditional global world frame is inferred for arbitrary children.',
      'composition': 'First reason over arbitrary full callee replies. Instantiate each BODY child CLOSED theorem at actual args/entry state; record the application. Only LEAF returned cases may remain hypotheses. Partial prefix proofs and whole-run theorems do not close a function.'}
    ledger['hypothesis_inventory'] = {
      'ruling': 'B-y item 3',
      'categories': ['Pre','documented_semantics','operator_semantics','typed_representation','FreshAllocationValidity','ClientLayout','PinnedConfig','leaf_returned_case'],
      'named_prefixes': ['PV_THR2_IntrinsicSemantics_', 'PV_STX2_IntrinsicSemantics_', 'PV_THR2_OperatorSemantics_', 'PV_THR2_TypedRepresentation_'],
      'named_constants': ["FreshAllocationValidity'", 'PV_OWN2_ClientLayout', 'PV_STX2_PinnedConfig'],
      'forbidden': ['BODY callee contract hypotheses', 'unlisted source read/receiver/alias/commutation/choice equalities', 'future success/value/pointee assumptions outside Pre', 'additional T fields'],
      'note': 'Type/carrier/argument parameters are distinct from proposition hypotheses. CLOSED receipts must inventory every proposition binder, including implicit/typeclass structures that carry propositions; no unchecked named Cases bundle.'}
    (EVID/'statements').mkdir(exist_ok=True)
    for row in ledger['rows']:
        path, i = row['path'], row['emitted_id']
        tag = 'OwnInit' if row.get('root') and path=='thread' else 'f'+str(i)
        safe = re.sub(r'[^A-Za-z0-9_]', '_', tag)
        ns = 'PV_FN_' + path.upper() + '_' + safe
        if row['kind']=='BODY':
            pre,post = DRAFTS[path][i]
            row['contract'] = dict(state='DRAFT', lean_pre=ns+'.Pre', lean_post=ns+'.Post', lean_contract=ns+'.Contract', lean_theorem=ns+'.contract',
              boundary='CALL_ENTRY_TO_RETURN' if not row.get('emitted_kind')=='CompositionRoot' else 'ORIGINAL_ENTRY_TO_OWNINIT_CASE_SPLIT',
              pre=pre, post=post, frame=ledger['contract_convention']['frame'], reply_branches=ledger['contract_convention']['reply_branches'],
              parameters=ledger['contract_convention']['parameters'], callee_policy=ledger['contract_convention']['composition'])
        else:
            fact = FACTS.get((path,i))
            row['leaf'] = dict(named_fact=fact, named_child='OF_child_f'+str(i) if isinstance(i,int) and path=='thread' and row['emitted_kind']!='Structured' else ns+'.full_reply_child',
              reply_domain='Arbitrary full reply of exact emitted return type: returned/error/fault/abort/divergence/pending, exact post-world/events and declared modifications; no fixed successful value.',
              disposition=row['disposition'], fact_source='lean/'+fact+'.lean' if fact else None,
              fact_status='documented semantics installed below endpoint; not a B-y raw-audited closed contract' if fact else 'named child retained; reply semantics/footprint obligations retained')
            if fact:
                get(row['source']['revision'], 'lean/'+fact+'.lean')
        for mod, thm in CANDIDATES.get((path,i),[]):
            srcpath='lean/'+mod+'.lean'
            src=get(row['source']['revision'],srcpath)
            if thm is None:
                thm=re.search(r'^theorem\s+(\w+)',src,re.M)[1]
            found=re.search(r'^theorem\s+'+re.escape(thm)+r'\b',src,re.M)
            if not found:
                raise ValueError((mod,thm))
            signature=src[found.start():src.index(':= by',found.start())]
            artifact=EVID/'statements'/(mod+'.'+thm+'.lean.txt')
            artifact.write_text(signature+'\n')
            fq=thm if thm==mod else mod+'.'+thm
            row['evidence'].append(dict(theorem=fq,branch=row['source']['branch'],revision=row['source']['revision'],source=srcpath,
                statement_artifact=str(artifact.relative_to(ROOT)), statement_kind='verbatim source signature; not claimed #print output',
                statement_sha256=hashlib.sha256(artifact.read_bytes()).hexdigest(),
                proves='Local returned run/prefix or ownership Post fragment; see complete statement. Not a B-y contract.',
                raw_audit='evidence/pv-evhB-20261103/thread-line/generated/session86/new-roots-audit/results.json' if path=='thread' else 'evidence/pv-stx-20261104/SLICE/raw99109/results.json',
                audit_qualification='Existing audit candidate; theorem-specific coverage must be checked before closure. No CLOSED credit inferred from aggregate pass.'))
        if row['evidence']:
            row['status']='PARTIAL'
            row['missing']=['Repackage at this function\'s own arbitrary call entry with entry facts in Pre.',
              'One theorem covers all reply branches and proves the caller-cell/heap frame by source shape.',
              'Instantiate every BODY callee contract instead of taking body dispositions/contracts as hypotheses.',
              'Theorem-specific complete raw audit and verbatim printed hypothesis inventory within B-y.']
        if path=='slice' and i==21:
            row['missing'].insert(0,'Call summary stops at source262 before byte copy, set_len and final return; QUniformReturn/ColumnViewReturn use a proof-view context, not the arbitrary call-entry contract. Derive bounded/overflow/fits facts from typed entry, preserve original registered witnesses.')
        if path=='thread' and i==124:
            row['missing'].insert(0,'Local run is complete on returned branches but retains local dispositions in WholeReturn; LocalReturn derives them. Nonnull allocation and leaf semantics must be composed into a complete branch/frame theorem; no arbitrary 12801 reply.')
        if path=='thread' and i==126:
            row['missing'].insert(0,'Entry root shape belongs in valid-Arc Pre and must be supplied by actual124 Post. WholeReturn still takes body222/child320 dispositions; derive these and instantiate222 contract, retain explicit final store.')
    ledger['contextual_evidence']=[dict(path='thread',theorem='PV_THR2_OriginalPacketSuccessful84.reached',
       source='lean/PV_THR2_OriginalPacketSuccessful84.lean',revision=ledger['source_pins'][-1]['revision'],
       classification='Whole-run F0-entry theorem, not a per-function closure. Reuse for OwnInit composition only.',
       statement='evidence/pv-evhB-20261103/thread-line/generated/session86/verbatim-statements.md'),
       dict(path='thread',source='evidence/pv-evhB-20261103/thread-line/generated/session95/verbatim-current-statement.md',
       classification='Later whole-run tagged q5 transport evidence, not a per-function theorem.'),
       dict(path='slice',source='evidence/pv-stx-20261104/SLICE/session72/remaining-obligations.md',classification='Explicit source262 frontier and absent complete call summary/loop.')]
    (ROOT/'design/PRIVACY-FN-LEDGER-20261108.json').write_text(json.dumps(ledger,indent=2)+'\n')
    print('Drafted',sum(r['kind']=='BODY' for r in ledger['rows']),'BODY contracts')

if __name__=='__main__': main()
