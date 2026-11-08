"""Read-only inventory; retain every native boundary and every emitted candidate.
No ledger, package or enumeration generator is modified.
"""
import json,lzma,pathlib,hashlib,importlib.util,sys
sys.dont_write_bytecode=True
P=pathlib.Path(__file__).parent; A=P.parent
spec=importlib.util.spec_from_file_location('enum','tools/pv-ledger/enumerate.py');en=importlib.util.module_from_spec(spec);spec.loader.exec_module(en)
x=json.loads(lzma.decompress((P/'thread-native.json.xz').read_bytes()));fs={f['function']:f for f in x['functions']}
rows=json.load(open('evidence/pv-ledger-20261108/enumeration.json'))['rows']
# Includes library-era semantic f207 -> f289 not in the original enumeration.
deps=json.load(open('evidence/pv-lib-20261107/DEPENDENCIES.json'))['rows']
edges={r['id']:set(r['callees']) for r in deps}
reverse={}
for r,children in edges.items():
 for c in children:reverse.setdefault(c,set()).add(r)
def ancestors(nodes):
 out=set(nodes);pending=list(nodes)
 while pending:
  for c in reverse.get(pending.pop(),[]):
   if c not in out:out.add(c);pending.append(c)
 return sorted(out & set(edges))
def nm(f):return '::'.join(p['Ident'][0] if 'Ident'in p else 'impl['+str(p['Impl'].get('Trait','inherent'))+']' if 'Impl'in p else '?' for p in f['item_meta']['name'])
calls={}
for f in fs.values():
 for c in en.walk(f['code']):
  if 'call_identity'in c:
   for t in en.target(c['callee'],'thread'):
    calls.setdefault(t,[]).append(dict(caller='thread:f'+str(f['function']),site=c['call_identity']['statement'],source_path=c['call_identity']['path']))
# Conservative raw-call propagation across installed native summaries. This is
# a MAY-affect relation, not a claim those nested requests were interpreted.
for target,occurrences in calls.items():
 if isinstance(target,int):
  for occurrence in occurrences:reverse.setdefault('thread:f'+str(target),set()).add(occurrence['caller'])
# Exact primitive candidates; body wrappers are explicitly distinguished.
meanings={9:'IntoIterNext9',10:'VecAppend10',93:'RangeNext93',167:'VecPush167',289:'CellReplace289',
 351:'FetchAdd351',581:'FetchSub581',557:'AtomicStore557',646:'AtomicBoolStore646',442:'MemReplace442',
 308:'PtrWrite308',364:'PtrWrite364',504:'CellSet504',641:'CellTake641',530:'CompareExchangeWeak530',555:'CompareExchange555',
 360:'ArcClone360',683:'WeakDrop683',457:'ScopeIncrement457',611:'ScopeDecrement611',486:'ArcDrop486',584:'ArcDropSlow584'}
footprints={
 9:'IntoIter.ptr or end',10:'destination RawVec/len and source len',93:'Range.start',167:'Vec.RawVec/len and element destination',289:'Cell transparent payload, including source-store pointees inside boxes',
 351:'AtomicUsize.v.UnsafeCell.value; ArcInner strong and ScopeData running count',581:'AtomicUsize.v.UnsafeCell.value; ArcInner strong/weak and ScopeData running count',557:'AtomicUsize.v.UnsafeCell.value; weak-count lock or other atomic',646:'AtomicBool.v.UnsafeCell.value; ScopeData.a_thread_panicked',
 442:'destination pointee',308:'destination pointee',364:'destination pointee',504:'transparent Cell payload := new; then Drop(old T), including destructor source writes',641:'transparent Cell payload := SpawnHooks::default() (first=None); old value returned without Drop',
 530:'AtomicUsize.v.UnsafeCell.value only on successful CAS; weak spurious failure preserved',555:'AtomicUsize.v.UnsafeCell.value only on successful CAS',
 360:'ArcInner.strong.AtomicUsize.v.UnsafeCell.value via Arc.ptr.NonNull.pointer',683:'ArcInner.weak.AtomicUsize.v.UnsafeCell.value, except dangling Weak',
 457:'ScopeData.num_running_threads; overflow path decrements again',611:'ScopeData.num_running_threads and conditional a_thread_panicked',
 486:'ArcInner.strong; last-strong branch also drops data and weak guard',584:'ArcInner.data destructor, then implicit weak decrement even on unwind'}
entries=[]
for i,meaning in meanings.items():
 sites=calls.get(i,[]);direct=[s for r in deps for s in r.get('sites',[]) if s.get('row')=='thread:f'+str(i)]
 affected=ancestors(['thread:f'+str(i)]+[c['caller'] for c in sites if c['caller']in edges])
 entries.append(dict(id='thread:f'+str(i),name=nm(fs[i]),emission='BODY' if 'body'in fs[i]['code'] else 'LEAF',
  installed_as_native=any(r['id']=='thread:f'+str(i) and r['kind']=='LEAF' for r in rows),
  sites=sites,affected_rows=affected,footprint=footprints[i],named_meaning='PV_THR2_LibrarySemantics_'+meaning,
  status='RETAINED-V1' if i in [9,10,93,167,289] else 'REQUIRES-V2-ACTION',
  endpoint_note='OwnInit may pass native boundary; exact entry reachability is not asserted' if 'thread:OwnInit'in affected else 'Nested emitted candidate; transport through enclosing native/type-drop boundary needs its own binding'))
loads=[]
for i in [18,121,123,127,129,368,371,455,528,582,600,763]:
 loads.append(dict(id='thread:f'+str(i),name=nm(fs[i]),sites=calls.get(i,[]),classification='NO-SOURCE-WRITE',reason='load/get/new/get_mut/into_inner/fence: returns value/reference or ordering only; new constructs a value, source assignment is emitted separately'))
# Boundary audit does not silently call arbitrary closures or opaque destructors pure.
writers={e['id'] for e in entries};reads={e['id'] for e in loads}
known_pure={3,7,8,130,134,165,217,268,269,277,278,279,280,312,313,319,320,344,410,453,455,456,612}
boundaries=[]
for r in rows:
 if r['kind']!='LEAF':continue
 rid=r['id'];i=r['emitted_id']
 if rid in writers:cls='SOURCE-WRITER'
 elif rid in reads or r['path']=='slice' and i!='builtin:Drop':cls='NO-DIRECT-SOURCE-WRITE'
 elif r['path']=='thread' and i in known_pure:cls='NO-DIRECT-SOURCE-WRITE'
 elif 'Drop'in rid:cls='TYPE-DEPENDENT-DESTRUCTOR-WRITES'
 elif i=='builtin:"BoxNew"':cls='EXISTING-OWNER-AND-SOURCE-ALLOCATION-ACTION'
 else:cls='NATIVE-WRAPPER-REVIEW'
 sites=[dict(caller=q['id'],**s) for q in deps for s in q.get('sites',[]) if s.get('row')==rid]
 boundaries.append(dict(id=rid,name=r['source_name'],classification=cls,sites=sites,affected_rows=ancestors([rid])))
# All raw native leaves retained, including opaque wrappers not classified as pure.
raw=[dict(id='thread:f'+str(i),name=nm(f),sites=calls.get(i,[]),classification=('SOURCE-WRITER' if i in meanings else 'NO-SOURCE-WRITE' if i in {18,121,123,127,129,368,371,455,528,582,600,763} else 'NOT-CERTIFIED-PURE; see boundary/candidate classification')) for i,f in fs.items() if 'body'not in f['code']]
drops=[dict(caller=r['id'],**s,affected_rows=ancestors([r['id']])) for r in deps for s in r.get('sites',[]) if 'Drop'in str(s.get('row',''))]
# Typed destructor metadata is retained from the emission, never guessed from a site number.
meta=json.loads(lzma.decompress((P/'thread-llbc.json.xz').read_bytes()))
values={}
def hashes(o):
 if isinstance(o,dict):
  if 'HashConsedValue'in o:values[o['HashConsedValue'][0]]=o['HashConsedValue'][1]
  for v in o.values():hashes(v)
 elif isinstance(o,list):
  for v in o:hashes(v)
hashes(meta)
types={t['def_id']:'::'.join(p['Ident'][0] for p in t['item_meta']['name']if'Ident'in p)for t in meta['translated']['type_decls']if t}
def typename(o):
 if 'Deduplicated'in o:return typename(values[o['Deduplicated']])
 if 'HashConsedValue'in o:return typename(o['HashConsedValue'][1])
 if 'Adt'in o:return types.get(o['Adt']['id'].get('Adt'),'builtin:'+str(o['Adt']['id']))
 if 'Ref'in o:return '&'+typename(o['Ref'][1])
 return str(o)
rawDrops=[]
for i,f in fs.items():
 for d in en.walk(f['code']):
  if d.get('opcode')=='Native.Drop':
   drop={k:v for k,v in d['native']['Drop'].items()if k!='on_unwind'}
   rawDrops.append(dict(caller='thread:f'+str(i),site=d['identity']['statement'],source_path=d['identity']['path'],native=drop,type_name=typename(drop['place']['ty']),affected_rows=ancestors(['thread:f'+str(i)])))
# Additional composite/type-dependent writers: no no-write claim is made for these.
extra={168:'JoinInner.packet.result.UnsafeCell.value is taken; Arc cleanup also writes counts',241:'copy_nonoverlapping destination may be a source-store pointee',248:'drop_in_place executes the selected destructor',308:'pointer-method write',322:'Drop::drop trait dispatch may execute Packet destructor and other captured destructors',325:'pointer-method drop_in_place',364:'pointer write',454:'spawn-hook TLS Cell::take/set and Arc clone/drop; provenance determines source/OWNER backing',549:'mem::drop executes the selected destructor',654:'Box::drop executes the pointee destructor before deallocation'}
extra.update({4:'Iterator::collect executes mutable iterator/captured callback, whose source effects need binding',14:'ordered_map_inner closure invokes the user callback; source effects need actual callback binding',214:'Thread::clone clones its Arc<Inner>; source count write if Inner is source-backed (OWNER operator path also exists)',
 122:'current_or_unnamed clones existing Thread or constructs TLS Thread; backing/provenance unresolved',
 128:'Thread::park delegates to Parker whose atomic state may be source-backed',
 225:'Parker::park changes the atomic parker state through Pin<&Parker>',
 669:'Parker::unpark swaps atomic state before a possible futex wake',
 309:'Parker::new_in_place writes through its destination pointer',
 296:'thread-local Storage::set replaces the stored payload through the receiver',
 369:'Option::take replaces the referenced Option by None without dropping its old payload',
 538:'pthread_attr_init writes pointed-to pthread_attr_t storage',
 544:'pthread_attr_setstacksize writes pointed-to pthread_attr_t storage',
 548:'pthread_create writes thread ID through its output pointer and invokes callback',
 648:'pthread_attr_destroy may invalidate the pointed-to attributes',
 510:'RawVec::deallocate invalidates backing allocation; source-cell lifetime mapping unresolved',
 622:'RawVec::finish_grow may allocate/reallocate source-backed storage; resource channel unresolved'})
# Mutable iterator interfaces and generic callbacks may modify a source receiver,
# captured references, or a destination. These conservative entries are NOT
# documentation facts or installed native meanings; every unresolved one stays open.
for i,f in fs.items():
 if 'body' in f['code']:continue
 name=nm(f)
 if any('::'+method in name for method in ['next','advance_by','advance_back_by','__iterator_get_unchecked','try_fold','fold']):
  extra.setdefault(i,'Iterator receiver/captured callback may write source-store state; exact emitted instantiation requires binding')
 if any(part in name for part in ['drop_glue','::call_once','::catch_unwind','::unwrap_or_else','::and_then','::map_or','::clone']):
  if i not in {196,283,377,408,451,567,568}:
   extra.setdefault(i,'Type-dependent destructor/clone/callback effects may write through captured source references; no purity claim')
 if name.endswith('::fmt') or any(part in name for part in ['::write_fmt','::write_str','::hash','::debug_struct','::finish']):
  extra.setdefault(i,'Formatter/hasher/output receiver or dispatched callback may mutate source storage; exact destination/type binding open')
for i,foot in extra.items():
 if any(e['id']=='thread:f'+str(i)for e in entries):continue
 entries.append(dict(id='thread:f'+str(i),name=nm(fs[i]),emission='BODY'if'body'in fs[i]['code']else'LEAF',installed_as_native=any(r['id']=='thread:f'+str(i)and r['kind']=='LEAF'for r in rows),sites=calls.get(i,[]),affected_rows=ancestors(['thread:f'+str(i)]),footprint=foot,named_meaning=None,status='TYPE-OR-WRAPPER-COMPOSITION-OPEN',endpoint_note='No arbitrary Store transformer is substituted. Exact destructor/type/provenance binding remains open.'))
rawSlice=[]
for n in [94906,94915,94917]:
 cohort=json.loads(lzma.decompress((P/f'slice-N{n}.json.xz').read_bytes()))
 for f in cohort['functions']:
  if 'body'not in f['code']:rawSlice.append(dict(cohort=n,id='slice:f'+str(f['function']),name=nm(f),classification='Recorded raw leaf; see installed native-boundary and typed Drop classifications'))
for boundary in boundaries:
 if boundary['id'] in {e['id'] for e in entries} and boundary['classification'] != 'SOURCE-WRITER':
  boundary['classification']='POTENTIAL-COMPOSITE-SOURCE-WRITER; EXACT-EFFECT-OPEN'
for item in raw:
 if item['id'] in {e['id'] for e in entries} and item['classification'] != 'SOURCE-WRITER':
  item['classification']='POTENTIAL-SOURCE-WRITER; EXACT-EFFECT-OPEN'

for entry in entries:
 if entry['id'] in {'thread:f486','thread:f584','thread:f683','thread:f322','thread:f248','thread:f325','thread:f549','thread:f654'}:
  entry['may_affect_via_typed_drop']=sorted({r for site in drops for r in site['affected_rows']})
  entry['drop_propagation_qualification']='Conservative type-dependent destructor footprint; exact emitted-type dispatch is not discharged.'
result=dict(schema=2,base='bbb785242b876aa943e9627aa46a7ffa350a860a860a'[:40],ruling='D984 thread-26 double-prime',criterion='ANY source-store cell, including BoxNew/Arc pointees; OWNER-only effects are separate',
 witness=dict(branch='codex/pv-lib-spec-20261107',revision='f2798a4fac4',module='PV_LIB_SPEC_F361ArcMachineGap',roots=['native_poll','count_unchanged','increment_impossible'],attempt=49735,site=12950),
 authority=json.load(open('evidence/pv-ledger-20261108/enumeration.json'))['source_pins'],
 source_writers=entries,read_only_counter_cell_operations=loads,native_boundaries=boundaries,all_emitted_thread_native_leaves=raw,all_emitted_slice_native_leaves=rawSlice,typed_drop_sites=drops,raw_thread_typed_drop_sites=rawDrops,
 refcell=dict(emitted_functions=[i for i,f in fs.items() if 'RefCell'in nm(f)],finding='No RefCell function occurs in this pinned emission; boxed Cell and UnsafeCell do occur. Generic Drop and opaque callback boundaries are not thereby pure.'),
 qualifications=['Conservative syntactic inventory; not a proof every site is reached on one execution.', 'Every installed native boundary is retained. NATIVE-WRAPPER-REVIEW and type-dependent Drop remain unresolved, not no-write classifications.', 'Raw nested primitive sites are not automatically requests of the installed machine. Enclosing native wrappers and typed Drop must bind their complete effects; adding primitive tokens alone is insufficient.', 'Slice raw copy destination is OWNER-backed M31 memory in the source7 path; reference construction and checks do not write source cells. Generic destructors retain type-dependent obligations.', 'No full corrected-machine adequacy, entry reachability, row closure or endpoint-premise removal follows.'])
result['base']='bbb785242b876aa943e9627aa46a7ffa350a860a'
(A/'store-write-leaves-v2.json').write_text(json.dumps(result,indent=2)+'\n')
lines=['# D984 source-store writer inventory v2','', 'Criterion: every source-store cell, including pointers into BoxNew/Arc allocations. This supersedes the v1 exclusion of Arc counts. The OWNER-aware base remains OwnInitInterpreterBridged.','', 'SPEC-C3: `codex/pv-lib-spec-20261107@f2798a4fac4`, `PV_LIB_SPEC_F361ArcMachineGap.native_poll/count_unchanged/increment_impossible`, focused49735: f360 at12950 leaves a source-store strong count unchanged. This is a local mismatch, not original-entry reachability.','', '## Writer candidates and exact emitted sites','', '| Function | Footprint | Sites (caller/site) |','|---|---|---|']
for e in entries:lines.append('| '+e['id']+' '+e['name']+' | '+e['footprint']+' | '+', '.join(c['caller']+'/'+str(c['site']) for c in e['sites'])+' |')
lines+=['','Each JSON entry lists affected ledger rows and whether it is an installed native boundary or a nested emitted candidate. Arc drop486/slow584 and scope decrement611 are emitted bodies; their primitive actions must not also be applied as whole-body summaries when those bodies are expanded. Weak drop683 is opaque. Typed Drop requests require dispatch by their emitted type, not a guessed function ID.','', '## Atomic reads, Cell and wrappers','', 'Atomic load127/129/528, fence582, Cell get18/600, UnsafeCell::get_mut368, Atomic constructors121/123, Cell::new371, UnsafeCell::new455 and Cell::into_inner763 do not write an existing source cell. Loads remain returned-value obligations. Cell replace289/set504/take641 and pointer writes308/364 are writers even if their receiver points inside a box. No RefCell function is emitted; this is not a purity result for arbitrary callback/destructor types.','', 'The JSON retains all '+str(len(boundaries))+' installed LEAF boundaries and all '+str(len(raw))+' raw thread LEAFs, with every known site and affected rows. '+str(sum(b['classification']=='NATIVE-WRAPPER-REVIEW' for b in boundaries))+' installed native wrappers and all type-dependent Drop sites remain REVIEW obligations. They are **not** certified no-write. In particular join168, Thread clone214, spawn hooks454 and scoped increment457 cannot acquire source-effect credit solely from a nested atomic table entry.','', '## Status and limits','', 'Inventory stage is conservative and incomplete at opaque-wrapper/type-drop effects. The v2 machine work must retain those open obligations. No prior native frame or graph at one of these writers transports unchanged. No new endpoint premise/T field, success restriction or arbitrary Store transformer is permitted. Complete wrapper/type-drop semantics before claiming the full D984 correction or continuing the requested caller histories.']
(A/'store-write-leaves-v2.md').write_text('\n'.join(lines)+'\n')
print(len(entries),'writers;',len(boundaries),'boundaries;',len(raw),'raw leaves;',len(drops),'typed Drop sites')

# Session coverage is part of the reproducible inventory output.
with (A/'store-write-leaves-v2.md').open('a') as coverage:
 coverage.write("\n## Compiled projection coverage (session5)\n\nThe final partial candidate is `PV_LIB_A_DropDispatchV2.step`, extending the\nOWNER-aware base through `OwnerStoreV3`. Original five plus17 new function\nprojections are compiled. `session5/STORE_ACTIONS.json` gives named meanings,\nexact source hashes, attempts, sites, affected rows and open coverage for every\ninventory candidate. Atomic loads127/129/528 have named returned-value facts;\nthey do not write source cells. Full backend/order/backing bindings are open.\n\nArc486/Weak683 are supported ONLY on source-selected nonlast counts; last,\ndangling, deallocation and typed payload Drop are not supplied. Cell504 is\nsupported ONLY for bool; generic old-value Drop is open. Transparent641 and\nnumeric-byte646 supersede the wrong wrapped/boolean-data drafts, which receive\nno source credit despite passing mathematical axiom audits. No missing full\nmeaning is replaced by a guessed Store transformer. The inventory's111 entries\nare conservative writer/callback candidates, not111 proved actual writers.\nEight further installed wrappers remain REVIEW, as explicitly listed in JSON.\n\nStrict raw47490 passed118 roots from28 new modules (standard axioms only),\nincluding superseded mathematical definitions for reproducibility. The audit\nproves no source/model adequacy. No slot status, row consumer, endpoint premise,\nT field, ledger or frozen specification was changed. D984 and complete caller\nhistories remain unfinished; unused focused IDs are not budget exhaustion.\n")
