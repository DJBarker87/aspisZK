"""Generate the 29 normative row documents from pinned ledger descriptions.

The extra clauses below are specifications, not proof or closure evidence.
"""
import hashlib,json,lzma,pathlib
E=pathlib.Path('evidence/pv-lib-20261107')
rows={r['id']:r for r in json.loads(lzma.decompress((E/'inputs/ledger.xz').read_bytes()))['rows']}
deps=json.loads((E/'DEPENDENCIES.json').read_text())
pins=json.loads((E/'INPUT_REVISIONS.json').read_text())
detail={
'slice:f0':('Each of the sixteen output columns has a distinct fresh OWNER identity and byte-for-byte equality with the corresponding ENTRY column; source and earlier columns survive later allocation/copy. The Foundation wrapper is rebuilt using its emitted aggregate kind. The Foundation construction caller discharges Source7EntryOwned with registry linkage, OWNER invariants and full typed reference validity.','Return the original Foundation by shallow copying its sixteen Vec descriptors. Positive-length source column 0 then shares its allocation with the result, violating freshness.'),
'slice:f1':('The const generic is 16. Output position i is the clone of input i, not an arbitrary permutation. A later failed allocation retains the prefix of requests/copies and never reports a complete array.','Return sixteen empty Vecs on an input with a nonempty first column.'),
'slice:f2':('Array-to-slice conversion preserves the source pointer/length. The clone generator captures that actual slice; from_fn/try_from_fn dispatch uses the emitted closure type, and all sixteen indices are generated in increasing order.','Clone column 0 sixteen times, even when column 1 has different bytes.'),
'slice:f4':('ArrayRepeat creates sixteen uninitialized UNION carriers, not initialized Vec values. On Continue initialize the corresponding slot exactly once. Never read an uninitialized slot. On Break preserve the residual and cleanup only the initialized prefix. The f11 uninhabited residual conversion abort is retained if that emitted branch is reached.','Report a complete array after initializing only slot 0.'),
'slice:f5':('Move the source capture into call_mut at the actual source index; invalidate/drop only the moved capture as the source does. Drop is the actual selected typed destructor, not a universal identity footprint.','Ignore the index and always call the generator at 0.'),
'slice:f6':('Entry capture uses the provider-owned tagged reference/aggregate representation. Derive the column reference by indexed projection from this capture. No late receiver/read premise. Preserve the source capture cells and typed source bytes while returning the actual Vec clone. A generic caller supplies its actual initialized prefix/capture state.','Return the capture array itself as the cloned Vec without invoking f13.'),
'slice:f7':('Use f8 provider definitions literally, including its capture-update and full explicit outcome store. After a successful call, the selected drop at source178 is the emitted f22 NeverShortCircuit closure destructor. Its no-foreign-store-write fact is proved by W2 TypedDestructor, not chosen as an identity delta.','Drop the freshly returned Vec and then return its dangling descriptor.'),
'slice:f8':('Unwrap only the source NeverShortCircuit closure wrapper. Invoke f6 at the actual argument and retain its capture update on the SAME outcome store before constructing the output wrapper.','Return NeverShortCircuit around a constant empty Vec.'),
'slice:f9':('Buffer/capture Pre includes their typed source representation, initialized prefix and remaining capacity. At index i, only slots below i are initialized. Call f8 once per source iteration; write its Continue value to i and advance exactly once. Break returns the exact residual with only initialized-prefix cleanup. No result is borrowed from another iteration.','Advance the index twice after the first Continue, leaving slot 1 uninitialized.'),
'slice:f13':('Build the source slice from the actual Vec pointer and length, clone the Global allocator at f20, and call f21 at the same pointer/length. Preserve the source descriptor, its allocation, and all initialized M31 bytes.','Return a shallow Vec descriptor aliasing the source allocation.'),
'slice:f21':('Use PV_STX2_ToVecCallReferenceEntry.Pre and its reference-valid OWNER definitions by name. Positive n allocates the actual M31 layout, copies exactly 4*n pre-state bytes into a fresh disjoint destination, performs set_len and returns the source Vec representation. For n=0 return the aligned non-null dangling zero-capacity Vec with no malloc/copy. Signed-size rejection, null allocation, resource failure/divergence/pending and copy exceptions retain their exact branches. Fix Pending to require completed=none and programs(callee)=none.','On an empty slice, claim pending at prefix11 merely because the ignored fallback handler says pending: prefix11 is an f31 BODY push with no native answer consumed.'),
'thread:f0':('Entry is OrderedFamiliesEntryOwned\' for the ACTUAL captures, including linked source address, typed validity, registry and numbering. Retain the full ordered result and all allocation, scope and OS effects on every source branch.','Return an empty family for n=1 and a worker producing a nonempty result.'),
'thread:f1':('Both worker/sequential routes remain in the domain. Iterate and collect at source arguments; retain order of scope/spawn/join and append. Native iterator f9 and Vec append f10 update their SOURCE descriptors through the concrete store-action interpreter. Resource demand witness independence is an obligation to prove, not an entry restriction.','Return results in reverse index order when two worker results differ.'),
'thread:f2':('The getter callback is the source token and uses CLOSED18 at the actual TLS reference; its returned boolean is the stored Cell boolean. TLS initialization/access failure is retained.','Always return false when the actual initialized TLS Cell is true.'),
'thread:f5':('The callback uses CLOSED207/CLOSED289 with actual Cell reference and replacement true. Return the source guard and retain the concrete Cell write, even though the callback return value alone does not expose it.','Return the guard without setting a previously false TLS Cell.'),
'thread:f6':('Construct ScopeData Arc with strong=weak=1 from CLOSED124/AtomicUsizeNew; use CLOSED126 for each actual dereference. Execute the f125 callback and source completion wait/park loop with all replies retained. Return its exact Result and explicit effects. Completion boundary never executes a lower caller suffix after div. No equality of summary/expanded activation counters.','Return callback success immediately while num_running_threads is nonzero, omitting the required wait/park path.'),
'thread:f15':('On next93 Some i execute exactly the source spawn of i with actual n/f/scope capture and then push its handle; None exits without allocating a ThreadInit for that iteration. Joins and result order are preserved. The range start and handle Vec header writes are actual source-store actions, not backend-only changes.','Treat a next93 None as Some 0 and allocate/spawn a worker.'),
'thread:f17':('try_with Ok returns its payload unchanged. try_with Err AccessError takes the actual panic_access_error child; under the pinned client panic strategy this is abort, with no normal value fabricated.','Convert an AccessError into an ordinary default boolean return.'),
'thread:f125':('Invoke f219 at the actual callback/capture arguments; transport the nested Result exactly. Under client panic=abort do not manufacture a caught-unwind success.','Return Ok(unit) without invoking the callback.'),
'thread:f166':('Builder fields are source literals. f270 receives actual scope and moved closure. On Ok return its scoped handle; on Err the source expect child takes its panic/abort path including any formatting allocation before diagnostic effects.','Convert spawn Err into an arbitrary success handle.'),
'thread:f170':('Both getter and setter contexts must be covered by the same row. Source TLS initializer468/469, Option as_ref277/ok_or278, Result branch279/from_residual280 and callback dispatch use provider constructors by name. Pure leaves preserve world on every answer (thread24). The setter executes f207 and the f289 concrete source-cell write; no arbitrary Effects field or write-definedness premise is admitted in MachineSpec.','Invoke the setter but restore the old Cell afterward; generic reachable-effects summaries can permit this, the source specification cannot.'),
'thread:f208':('Unpack the source scope closure captures, pass the actual scope reference to f15, and propagate every result, store and effect without taking a second callback reply.','Call f15 with a different scope reference than the actual captured scope.'),
'thread:f219':('The preserved intrinsic318 runs do_call316 ONCE with actual data; ManuallyDrop/new/take/into_inner use emitted representations. The callback result is stored in its argument-reachable result cell. Full Result arms and panic=abort are retained.','Produce an arbitrary returned intrinsic reply without invoking do_call.'),
'thread:f220':('Unwrap AssertUnwindSafe using its source aggregate, then invoke f208 with the same argument tuple; preserve callback effects and its exact nested Result.','Wrap a constant result without running the enclosed closure.'),
'thread:f270':('Use Builder.name and stack_size, clone the actual Scope Arc with nonzero strong count derived from construction, and pass the moved worker closure to f361. On source Err retain the exact error and earlier callback/Thread/Box allocations, not a post-success-only allocation arm.','On an OS spawn error, erase the preceding callback and ThreadInit allocation events.'),
'thread:f316':('Read callback/data via their typed source pointers, invoke CLOSED-or-pending220 at actual arguments, then write the returned result to the source union/result cell. That caller-visible cell delta is explicit, not FrameLocal fiction.','Run the callback but leave the caller result cell unchanged.'),
'thread:f318':('This is a HIGHER-ORDER intrinsic, not an arbitrary-result leaf. Call f316 once with the data pointer. On normal return use the intrinsic success code and actual output cell. Under pinned panic=abort, callback panic terminates and no unwind handler returns normally. Pending/failure/divergence stays at the actual callback site.','Return the intrinsic success code without calling f316 or writing its result cell.'),
'thread:f361':('The full function boundary is AFTER spawn_unchecked returns, not at OwnInit. Entry includes W3 NameEntryValidity.NameOwned (both Option constructors, UTF8 bytes, registry and validity) and ScopeEntryValidity.Shape. Track Thread/CString, Packet Arc, callback Box allocation13923, casts14119/14121, Unique/Box wrappers and ThreadInit allocation14756. At14756 derive decodeBridged from the actual registry/vtable bridge; consume allBridged and SourceInitBoxOwnership. Preserve the later spawn success AND Err arms and every earlier allocation prefix.','Allocate a ThreadInit containing a constant callback pointer rather than the actual callback Box data/vtable.'),
'thread:OwnInit':('This is an ORIGINAL-ENTRY milestone spec, not an f0 return spec. Its boundary overrides the common function boundary: stop at the actual ThreadInit allocation/store milestone14756 on each spawning Some iteration; for None there is no box, and for earlier stop retain that actual site. Some i is in the CONCLUSION case split, never Pre. Derive the target source fields and registry binding on ONE continuous history. Consume PV_THR2_OwnInitActualAllocationOwned.allBridged and SourceInitBoxOwnership by name; never the obsolete .all or bare-pair Shape premise. Later f361 spawn return is a separate row obligation.','Assert OwnInit by assuming old decode succeeds on the tagged source Box: that antecedent is impossible at14756 and proves no actual allocation ownership.')}
specific_diff={
'thread:f6':'f6Joins has original-machine PrefixIdentity/GlobalOriginalTransport and pending DeliveryInterfaces.f125 targets; none is an inhabitant of the full contract. New spec fixes the corrected store-action machine, carries thread25, and requires complete loop initialization/preservation. Existing BeforeDelivery is retained; no successful-only BeforeReturn boundary is reintroduced.',
'thread:f361':'f361Statement has sourceStep and changes parameters, original IntrinsicState executions, scopeOwned conditional shape and Pre without the final typed NameEntryValidity/numbering clauses. New spec binds the actual enlarged interpreter, source write meanings and name/Scope entry validity, requires concrete source/binary bridge adequacy and all joins to return. Old statement and its later helper extensions remain unchanged.',
'slice:f21':'ToVecCallSpecification already states MachineSpec, reference validity, numbered entry and positive ownership. Pending omits completed=none and native-dispatch resolver test (session88 actual_entry_false_pending). Post existential finite fuel alone has no separate infinite-divergence alternative; undefined is excluded without an adequate source binding. It constrains internal state after abort; new observable abort carries events only. New spec preserves zero/positive/error branches and requires first ACTUAL boundary.',
'thread:f170':'f170Statement takes arbitrary Effects D, has an older partial numbering Pre, and summary outcomes rather than a proved actual corrected-machine execution. OriginalStatement adds resolver/request equations but still targets the original interpreter; source-store interpreter later helpers remain conditional on local path/age facts. New spec derives those facts internally, binds the concrete write meaning and no write-definedness/Store premise. It uses exact source constructor facets and every pending boundary.',
'slice:f7':'The preliminary Statements.Pre fixes resolver clauses and omits the full typed generator/capture domain; Through8/OtherComposition and DropLive are named pending targets. W2 session10 adds TypedContract.Pre, actual typed f22 destruction and a conditional runtime contract, but f6SourceFrame.Contract, carrier/runtime binding and joint nonemptiness are still pending. New spec retains these as provider/caller discharge obligations, not proof assumptions hidden in Pre.'}
lines=['# PLIB frozen row specification index','',
'Target not yet established. Revision 1: 29 specifications; no ledger closure or row-proof consumption.',
'','Read PSPEC_COMMON.md as part of EVERY row. Inputs are pinned by INPUT_REVISIONS.json and INPUT_MANIFEST.json. This is a normative Markdown contract package; it is not a claim that 29 Lean contract declarations or candidates compiled.',
'','| Row | Specification | Source function |','|---|---|---|']
for rid in [r for r in deps['order'] if rows[r]['status']!='CLOSED']:
 r=rows[rid]; slug=rid.replace(':','_'); path=E/f'PSPEC_{slug}.md'; c=r.get('contract',{})
 pre=c.get('pre','Actual catch_unwind callback pointers, data pointer and result storage, with valid source-typed captures.')
 if rid=='thread:OwnInit':pre="OrderedFamiliesEntryOwned' for actual public n and captures; NO next93 returned/Some premise."
 post=c.get('post','Execute the callback intrinsic and preserve its source success code, output cell, abort and stopped branches.')
 alg,reject=detail[rid]
 provider=''
 if rid in specific_diff:provider=specific_diff[rid]
 elif rid in ['thread:f2','thread:f5','thread:f17']:
  provider='W4 Statement/OriginalStatement modules describe conditional summary/caller composition. Their dependencies are still PARTIAL and their actual source-store-machine transport is unfinished. This spec uses the actual enlarged interpreter, thread25 and exact provider constructors; no conditional summary is treated as proof of the row.'
 elif r['status']=='PARTIAL':
  provider='The ledger PARTIAL evidence is a prefix/conditional contract, not this full own-entry all-outcome specification. The common machine/entry/frame/boundary clauses add thread22/23\'/25/26/27 explicitly. Retain the provider representation by name; a new consumer representation is forbidden. No implication from the partial evidence to this specification is claimed.'
 else:provider='The pinned ledger has no complete compiled Pre/Post contract for this OPEN row. Prefix helpers are supporting evidence only. The common clauses supply the machine, reference/OWNER/numbering invariants, first boundary, all-answer observation and frame. No existing theorem is being silently restated as a full proof.'
 sites='\n'.join(f"| {s['site']} | `{s['row']}` |" for s in r['call_sites']) or '| composition | `thread:f0` |'
 src=r['source']
 text=f'''# PSPEC {rid}, revision 1

Status: SPECIFICATION ONLY; frozen by FREEZE.json. Ledger remains {r['status']}.

Source: `{r['source_name']}`. Frozen syntax `{src.get('syntax')}` at `{src['revision']}` on `{src['branch']}`. Exact signature and call metadata: DEPENDENCIES.json. Source artifact is retained compressed in inputs/.

## Pre and named machine

`Pre_{slug}`: {pre}
Conjoin ALL entry clauses in PSPEC_COMMON.md, using the actual typed arguments and arbitrary lower/suspended callers. `MachineSpec_{slug}` is the common machine specification specialized to this pinned body and the slots below. No child-success, future read, decode-success, activation-counter equality or desired-store hypothesis.

## Post, frame and complete arms

`Post_{slug}`: {post}

{alg}

Every returned Ok AND Err payload, fault, process abort, divergence and ACTUAL pending answer obeys PSPEC_COMMON.md. `Frame_{slug}` is its source-cell/heap/OWNER/event frame at THIS row's completion or delivery, never beyond it. Abort has event prefix only. Allocation and reservation are explicit environment replies. Each transitive reached allocating child retains allocation-before-later-Err and allocation-before-log arms; no blanket may-abort alternative.

## Child slots at source call sites

| Site | Required child |
|---|---|
{sites}

Each BODY call is one D877 summary step at the same arguments, with a graph-of-function child law. The map supplies the CLOSED root or explicitly flags the gap. Call-domain discharge belongs to this row, not an extra hypothesis. Named leaf semantics and runtime adequacy remain in their recorded inventory.

## Comparison to current package statements

{provider}

Common before/after differences for ALL rows: the ledger's drafted return boundary is bounded by own completion/delivery; process abort loses post-abort state; OWNER has fresh-frame, non-null/alignment and native-ghost framing clauses; entry has live numbering; cross-callee Store/counter equality is removed. These are thread23\'/slice9/10/11\'/thread25/27 corrections to interface form, with the actual source behavior retained. Existing CLOSED rows are not edited or withdrawn.

## Rejection example

{reject}

This is a normative counterimplementation example, not a new compiled counterexample theorem. Resource replies in the example grant the requests needed to reach the distinguishing output; that is an admissible environment, not a success restriction on this specification.
'''
 path.write_text(text)
 lines.append(f"| `{rid}` | [PSPEC_{slug}.md](PSPEC_{slug}.md) | `{r['source_name']}` |")
(E/'PSPEC_INDEX.md').write_text('\n'.join(lines)+'\n')
(E/'SPEC_CORRECTIONS.md').write_text('# Frozen specification corrections\n\nNo post-freeze corrections. Initial known package defects are documented in TOP_COMPOSITION.md and the row comparisons.\n')
files=sorted(E.glob('PSPEC*.md'))
(E/'FREEZE.json').write_text(json.dumps(dict(version=1,source_inputs='INPUT_MANIFEST.json',
 files={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
 policy='Demonstrated error against frozen source; exact before/after and witness in SPEC_CORRECTIONS.md'),indent=2)+'\n')
print('Frozen',len(files),'specification files, including common and index')
