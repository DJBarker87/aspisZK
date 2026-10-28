"""Build the evidence index from the pinned git census and diagnostic goto graphs."""
import json,pathlib,subprocess,re,collections,hashlib
E=pathlib.Path(__file__).resolve().parent
C=pathlib.Path('/private/tmp/pv-kscan-cache-20261028')
if not C.exists(): C=E
load=lambda n:json.loads((C/n).read_text())
heads=json.loads((E/'heads.json').read_text());T=load('tree-index.json');R=load('receipt-census.json');L=load('passing-logs.json')
proc=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
def gitblob(b):
 proc.stdin.write((b+'\n').encode());proc.stdin.flush();h=proc.stdout.readline().split();s=proc.stdout.read(int(h[-1]));proc.stdout.read(1);return s.decode(errors='replace')
# Canonicalize the six duplicate collection logs from the same l2b runs.
L=[x for x in L if not ('pv-l2b' in x['path'] and '/kani/' not in x['path'])]
G={}
for p in (E/'diagnostics').glob('[KR]*/goto-scan.json'):
 for h in json.loads(p.read_text()):G.setdefault(h['harness'],[]).append((p.parent.name,h))
# Use qualified names only inside their original proof family.
family_run={'pv-cblib-20261027':'K02','pv-alib-20261027':None,'pv-cb-20261026':'K07','pv-cb3-20261026':'K06','pv-l2b-20261027':'K05','pv-dlib-20261028':'K08','batch-effects3-20261026':'K09','native-p6-20261026':'K10'}
rows=json.loads(gitblob(T['research']['evidence/privacy-recount-20261026/recount6/rows6.json']))
# Exact row scope association; other families support already-open native/effect obligations.
def rowmap(f,h):
 if f=='pv-alib-20261027':return ['V184'] if 'pop' in h else ['V233']
 if f=='pv-dlib-20261028':return ['V237']
 if f=='pv-cblib-20261027':
  if 'pathbuf_borrows' in h:return ['V177','V180']
  if 'op34' in h:return ['V185']
  if 'op35' in h:return ['V186']
  if 'capacity' in h:return ['V181']
  if 'push' in h:return ['V182']
  if 'string_path' in h:return ['V179']
  if 'join' in h:return ['V178']
  if 'pop' in h:return ['V184']
  if 'array' in h:return ['V187']
  return ['V232','V237']
 if f=='pv-cb3-20261026':
  if 'wide' in h or 'all_carriers' in h:return ['V195']
  if 'boundary' in h:return ['V219']
  if 'pole' in h:return ['V264']
  return ['V256','V260']
 if f=='pv-cb-20261026':
  for word,rr in [('take',['V169']),('pathbuf',['V177','V180']),('path_join',['V178']),('string_scalar',['V179']),('string_ascii',['V179']),('string_path',['V179']),('push',['V182']),('capacity',['V181']),('default',['V186']),('empty',['V185']),('pop',['V184']),('reserve',['V183'])]:
   if word in h:return rr
  return ['V163','V164']
 if f.startswith('pv-l2'):return ['V352','V354','V357','V360']
 if f.startswith('pv-inv'):return ['V380-inversion']
 if f.startswith('pv-rw') or f=='pv-join-20261026':return ['V163','V164','V240']
 if f.startswith('batch-effects'):return ['V163','V165','V167']
 if f.startswith('pv-runjoin') or f.startswith('pv-srcid'):return ['V163','V165','V167','V389']
 if f in ['op4-p6-20261025','native-p6-20261026']:return ['V389']
 return ['V163','V165','V167','V389']
def classify(k,h):
 name=h['harness'];copies=h['copy_paths'];body=h['source_body']
 if not copies:return ('NO_REACHED_COPY',False,False,None,'No memcpy/memmove node reachable from the selected harness root in the goto call graph.')
 if k=='K02' and name=='path_checks::pathbuf_borrows':return ('EXEMPT',False,False,'call-name overapproximation','All copy paths are allocation growth helpers. bytes() pushes n<=4 u8 into an empty Vec; first capacity is at least8, and no later grow/realloc is admitted. OsString::from_vec, PathBuf ownership conversion and reference consume/view the same buffer.')
 if k=='K07' and name=='checks::reserve_zst_overflow':return ('EXEMPT',False,False,'call-name overapproximation','Vec<()> has usize::MAX capacity; zero-size reservation does not reach the grow/copy branch.')
 if k=='K10' and name=='NP6_lengths::NP6_static_length_rejection':return ('EXEMPT',False,False,'rejects before the copy on the admitted domain','932-byte frame rejects at row25 validation before allocation or boxing. Graph copy paths are only downstream grow/shrink helpers.')
 if k=='K10':return ('EXEMPT',False,False,'call-name overapproximation','All root-to-copy paths pass through allocator grow/shrink/realloc. heap::uninit reserves exactly1 on an empty Vec, sets len1 and boxes at cap1. heap::filled reserves exactly3 empty, resizes within cap3 and boxes at len=cap3; source/reference and construction/step harnesses use these fixed shapes. Thus no nonempty allocation is grown/shrunk and no copy builtin is reached. Source snapshots and graph copy predecessors are retained. Array/struct assignments are not copy builtins in these goto models. Historical allocator diagnostics K026-028 remain excluded.')
 if k=='K02' and name=='checks::empty_u8':return ('EXEMPT',False,False,'call-name overapproximation','n<=8 u8 pushes fit the first allocation (capacity at least8); initial allocation has no old buffer to copy.')
 if k=='K07' and name=='checks::empty16':return ('PROPERTY_INDEPENDENT',True,False,None,'Setup to_vec copies bytes, but the sole property is is_empty==len==0; it does not inspect copied element results.')
 if k=='R01' and name=='checks::acceptance_exact':return ('PROPERTY_INDEPENDENT',True,False,None,'Assertion concerns OR-scan versus zero comparison on the same copied buffers; it does not assert correspondence with raw input. Copy preservation cannot be inferred from this PASS.')
 if k=='K04':return ('EXPOSED',True,True,None,'n<=129 includes rb>=16 and rt>=16. Repeated Vec::push grows an existing byte buffer. Arbitrary block/tail coordinate assertions inspect the preserved bytes after reallocation.')
 return ('EXPOSED',True,True,None,'A nonzero content copy/clone or append is on an admitted source path and the assertion compares resulting contents. Goto root-to-builtin paths are retained. This suspends the native PASS link, not the mathematical reference theorem.')
items=[]
for x in L:
 f=x['path'].split('/')[1];parent=x['path'].rsplit('/',1)[0]
 for harness in x['pass_harnesses']:
  candidates=[]
  for r in R:
   if not r['path'].endswith('receipt.json'):continue
   if r['path'].rsplit('/',1)[0]==parent:
    try:v=json.loads(r['content'])
    except ValueError:continue
    candidates.append((r,v))
  if not candidates:
   for r in R:
    if r['path'].split('/')[1]==f and harness in r['content'] and (r['path'].endswith('receipt.json') or r['path'].endswith('.json')):
     try:v=json.loads(r['content'])
     except ValueError:continue
     if isinstance(v,list):
      for vv in v:
       if isinstance(vv,dict) and vv.get('harness')==harness:candidates.append((r,vv))
     elif isinstance(v,dict) and any(k in v for k in ['target','command','harness']):candidates.append((r,v))
  candidates.sort(key=lambda t:(not t[0]['path'].endswith('receipt.json'),len(t[0]['path'])))
  rv=candidates[0] if candidates else None
  cmd=rv[1].get('target',rv[1].get('command')) if rv else None
  info=dict(harness=harness,pass_output=x['path'],pass_output_blob=x['blob'],refs=x['refs'],receipt=rv[0]['path'] if rv else None,receipt_blob=rv[0]['blob'] if rv else None,command=cmd,source_revision=(rv[1].get('source_revision',rv[1].get('revision')) if rv else None),tool_pins={'kani':'0.67.0','cbmc':'6.8.0','pin_scope':'Historical version/config pins, not a fresh equality check of historical tool binaries. Diagnostic binary SHA256 values are in diagnostics/tool-pins.json.','output_version_lines':x['pins']},ledger_rows=rowmap(f,harness),ledger_relation='Candidate/source or supporting native-association scopes. An OPEN row is not a claimed closure; exact closure consequences are recorded separately.',copy_builtin_reached=None,property_depends_on_copy=None,exemption=None,status='UNRESOLVED',reason='Original PASS log is terse or lacks a reached-call/trace inventory. No source-name-only exemption is awarded.',diagnostic=None)
  gs=[(k,h) for k,h in G.get(harness,[]) if family_run.get(f)==k or f=='pv-alib-20261027' and k in ['K03','K04']]
  if not gs:gs=[(k,h) for k,h in G.get(harness,[]) if k=='R01']
  if gs:
   k,h=gs[0];status,reached,depends,exemption,reason=classify(k,h)
   info.update(status=status,copy_builtin_reached=reached,property_depends_on_copy=depends,exemption=exemption,reason=reason,diagnostic={'run':k,'harness':harness,'metadata_and_paths':f'diagnostics/{k}/goto-scan.json','graph':f'diagnostics/{k}/'+h['graph_file'],'goto_sha256':h['goto_sha256'],'graph_sha256':h['graph_sha256'],'bound':h['metadata']['attributes']['unwind_value'],'identity_scope':'Retained source package relocated for diagnostic codegen; qualified harness/call chain. No SAT replay, no restoration of native credit.'})
  if f=='native-p6-20261026' and re.search(r'NP6_K02[678]/',x['path']):info['evidence_use']='EXCLUDED historical allocator diagnostic; not one of the 16 accepted links'
  else:info['evidence_use']='Historical PASS census; may be superseded or partial. Exact row scope is preserved.'
  items.append(info)
# Per-row consequences are separate from support-level PASS exposure.
suspended={'V178':'Native Path::join to owned/slice reference uses reached byte append/copy. The proved JoinAdapter/reference law does not prove the shipped library body without this P6 association.', 'V179':'The String-to-Path native gate constructs the admitted String through a reached raw.to_vec copy; the later view assertion observes that storage. The emitted owned-carrier law remains valid but does not independently supply arbitrary native input coverage.', 'V182':'Native push_str and reference extend_from_slice depend on reached copies, including input construction. UTF-8/Result transport alone does not supply the shipped native append link.', 'V195':'wide_flat calls the shipped WideExact::to_le_bytes, whose fixed slices lower to memcpy; the asserted 32-byte equality depends on copied data. Raw.wide_bytes_flat is an owned reference, not extraction of the shipped serializer.', 'V233':'The scalar/coordinate gate builds flat reference byte vectors by push. Admitted lengths grow existing buffers, and the compared bytes depend on reallocation copies. The unbounded Lean law is for the explicit extracted reference/storage carrier; it does not independently justify the shipped unsafe pointer/slice association.'}
independent={'V184':('STANDS','PV_AL_MoveClosure.complete / PV_AL_MoveWorld.source_reference and reference_memory; STRUCTURAL-POP-GATE.json pins pop/remove/try_remove. MoveNativeValue and MoveMemory prove last-index/read/header/zero-copy effects for arbitrary payload Type and width. The clone-based bounded harness is exposed and unavailable, but this later structural/library proof already supplies the retained candidate scope. Raw pointer/compiler/deployment adequacy stays outside that scoped closure.'), 'V265':('STANDS','PV_AL_CircleNative.source_reference and PV_AL_CircleSelected.native_source, STRUCTURAL-CIRCLE-GATE.json, audits37698/37699. Ruling(k) structural route, 8712 comparisons finite only; no Kani PASS is used.'), 'V177':('STANDS','Current pathbuf_borrows gate is exempt: n<=4 construction fits initial allocation; only generic growth helper copy call names appear. Older to_vec-based pathbuf_borrow16 PASS is exposed and superseded. Original native layout/lifetime/world/deployment limits retained.'), 'V180':('STANDS','Same current pathbuf_borrows no-reallocation argument as V177. Older copying gate is unavailable; current scoped view/ownership route retains its bounds.'), 'V181':('STANDS','Both split_checks::string_capacity and resume8::capacity_bytes goto graphs have no reachable copy builtin. Empty-byte extraction/adapter law retains allocation/world/unbounded deployment limits.'), 'V185':('STANDS','Credited op34_exact_word constructs vectors and tests is_empty against len only. Copied element values are not an input to either boolean. Earlier empty16 setup copies do not establish a content law and are property-independent under K-1. Original bounded scope retained; exact_word goto graph remains uncollected.'), 'V186':('STANDS','Native Vec::default length/capacity are zero; direct empty constructor route, no element values or copying. Earlier default_vec/default_u8 graphs have no copy. Original exact_word gate was not reconstructed; no broader native theorem inferred.'), 'V237':('STANDS','Recount6 remains OPEN. Live dlib fixed constructor and arbitrary-core default gates have no reached copy node; proposed structural/extracted native_callback remains an unadopted scoped proposal, not an original-row promotion.')}
consequences=[]
for r in rows:
 rid=r['id'];before=r.get('recount6_status');st='STANDS';why='No K-1-dependent closure identified at the retained recount6 scope. Existing OPEN/REDUCED/data/model status is preserved; STANDS does not close an open row.'
 if rid in suspended:st='SUSPENDED';why=suspended[rid]
 elif rid in independent:st,why=independent[rid]
 elif r.get('closure_theorem'):why='The recorded closure is an extracted source/structural/Lean equation at its stated candidate scope, with native/deployment obligations retained. No affected Kani link was identified as a necessary premise of this closure; support-level unresolved gates are not promoted.'
 consequences.append(dict(row=rid,name=r['name'],before=before,consequence=st,reason=why,closure_theorem=r.get('closure_theorem'),baseline_evidence=r.get('recount6_evidence'),supporting_passes=[i for i,x in enumerate(items) if rid in x['ledger_rows']],reverify_when_validated_stub_available=rid in suspended or rid=='V184'))
counts=dict(collections.Counter(x['status'] for x in items))
reverify_support=sorted(set(rr for x in items if x['status']=='EXPOSED' for rr in x['ledger_rows']))
result=dict(schema='StreamB-K1-exposure-v1',task='LOG D346',branch='codex/pv-kscan-20261028',heads=heads,baseline='0c282f7952',ruling='pv-common.txt LEAD RULING(r),2026-10-28 02:25 UTC',method='KDX reached-call graph plus admitted-domain/property review; source/name candidates alone never certify reachability or exemption',coverage='Complete selected Stream-B evidence-directory historical PASS log census at the eight pinned heads; reached-call adjudication remains INCOMPLETE for entries explicitly UNRESOLVED/GROWTH_ONLY_UNRESOLVED. No no-copy conclusion is drawn for them.',target='not yet established',budget=dict(kani=10,kani_limit=10,lean=0,lean_limit=10,native_builds=0,notes='K01 CLI rejection charged; K02-K10 optimized codegen only, not SAT verification. Separate capped read-only graph recovery for K02 and surviving historical artifacts R01. No false-pass reproduction or stub.'),counts=counts,pass_count=len(items),passes=items,exposed=[i for i,x in enumerate(items) if x['status']=='EXPOSED'],unresolved=[i for i,x in enumerate(items) if x['status'] in ['UNRESOLVED','GROWTH_ONLY_UNRESOLVED']],suspended_rows=list(suspended),reverify_rows=list(suspended)+['V184'],historical_support_rows_to_reverify_if_reused=reverify_support,final_heads=json.loads((E/'heads-end.json').read_text()),head_delta_review='head-delta-review.json (no new PASS at reviewed end heads)',row_consequences=consequences,negative_scope_findings={'V172-V176':'No credited Kani native closure; original OPEN/REDUCED IO/effect/erasure scope retained.','V265':'No Kani gate; structural route.','pv-route2/pv-batch1/pv-batch2/pv-batch3':'No successful Kani PASS output in the pinned evidence directories; extraction/structural/native fixture gates retain their own status. Historical batch-effects and batch-effects3 PASS records are included separately.','pv-b3p6':'At pinned head only op133 setup failures/running gate, no PASS recorded.','pv-reach/pv-l2c':'No new PASS log found outside inherited corpus at pinned heads.'})
(E/'scan.json').write_text(json.dumps(result,indent=2)+'\n')
print(result['pass_count'],counts,'suspended',list(suspended))
