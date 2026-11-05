"""Retain entry admission and add the two exact same-function error occurrences."""
from pathlib import Path
import json,lzma,hashlib,copy,types,subprocess,sys,time,resource
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1];P=E.parent/'slice-d-entry4-20261106';J=E.parent/'slice-d-entry3-20261106';start=time.monotonic();sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_text())
def put(n,x):(E/n).write_text(json.dumps(x,indent=1)+'\n')
subprocess.run([sys.executable,str(E/'NIJ_entry_check.py')],check=True);subprocess.run([sys.executable,str(E/'NIJ_error_check.py')],check=True)
entryrev='a7ca0d44679'
def entry(n):return json.loads(subprocess.check_output(['git','show',entryrev+':'+str((E/n).relative_to(R))],cwd=R))
prior=entry('NIJ_LEDGER_DELTA.json');priorc=entry('NIJ_CLOSED.json');assert prior['new_closed_rows']==['TX2:202']
put('NIJ_ENTRY_STAGE_PIN.json',dict(revision=entryrev,files=[dict(path=str((E/n).relative_to(R)),sha256=sha(subprocess.check_output(['git','show',entryrev+':'+str((E/n).relative_to(R))],cwd=R))) for n in ['NIJ_LEDGER_DELTA.json','NIJ_CLOSED.json']]))
basepath=E.parent/'ledger10-20261106/NHO_LEDGER.json.xz';data=lzma.decompress(basepath.read_bytes());base=json.loads(data);by={r['row']:r for r in base['rows']};v=(E/'NIJ_NFK_validate.py.txt').read_bytes();assert sha(v)==prior['unchanged_NFK_validator_sha256']
n=types.ModuleType('NIJ_error_NFK');n.__file__=str(E/'NIJ_NFK_validate.py.txt');exec(compile(v,n.__file__,'exec'),n.__dict__);n.BASE_CREDITS=base['NEZ_credits']
candidates={};certs={};inherited=[]
for root,prefix in [(J,'NHJ'),(P,'NHY')]:
 cc={c['id']:c for c in read(root/(prefix+'_CLOSED.json'))['functions']}
 for row in read(root/(prefix+'_LEDGER_DELTA.json'))['rows']:
  rid=row['row'];assert rid not in candidates;candidates[rid]=(prefix,copy.deepcopy(row));certs[rid]=cc[row['selected_claims'][0]];inherited.append(rid)
for row in prior['rows']:candidates[row['row']]=('NIJ',copy.deepcopy(row));certs[row['row']]=priorc['functions'][0]
a=read(E/'NIJ_ERROR_ASSOCIATION.json');raw=read(E/'NIJ_stage2_audit/proof1.json');scan=read(E/'NIJ_stage2_audit/scan_summary.json');fx=read(E/'NIJ_stage1_audit/fixtures.json')
assert raw['same_optimized_binary_sha256']==fx['same_optimized_binary_sha256'] and fx['exit_status']==raw['exit_status']==0
assert len(fx['results'])==8 and all(x['equal'] for x in fx['results'])
assert all(x['equal'] and set(x['walked_axioms'])==set(x['collect_axioms'])<={'propext','Classical.choice','Quot.sound'} for x in raw['results'])
assert scan['dangling']==scan['incompatible_owners']==scan['import_mismatches']==0
c=dict(id='NIJ::error',subject='programs/r1-cost-probe/src/lib.rs::error',route='y/al/ak/an: eight actual frozen roots with real String writer, calibrated Std metadata, byte-exact syscall and deallocation/frame packets',model_theorem='NIJ_ErrorJoin.source',root_domain='Every deployed verifier::Error constructor (all eight), fixed literal r1:error:{:?}; no parent/callee successful-output premise. Native Arguments::as_str None domain derived by NHY_K111/112 for every case; actual formatter/writer/drop execute. Existing valid fresh allocator and runtime/ABI/Std realization retained, no totality claim.',inner_hypotheses_remaining=[],native_passes=[x['positive'] for x in a['instantiations']]+[x['cleanup_positive'] for x in a['instantiations']],matched_controls=[x['negative'] for x in a['instantiations']]+[x['cleanup_negative'] for x in a['instantiations']]+['NIJ_K109'],callee_laws={'compiler metadata':'Exact all-eight literal Native NHY_K111/112:18/None; explicit Std None constructor reference NIJ_ArgumentMetadata.image/as_str_none/capacity/choose. Global std as_str semantics not assumed; fixed caller domain only. Wrong Some(corrupted) control NIJ_K109 fails at actual syscall byte assertion.', 'Debug callback/String':'Per(al) all eight constant Error::fmt instantiations; actual String vtable and real write_str/append/growth execute in every root K070..086, Parse stability K072. Separate String dispatch K005..021, append/growth K023..038 and writer K040..055, all paired. Exact KMX patch; DebugLog never selected.', 'logging':'Exact message bytes at actual sol_log &str call, unit reply unchanged; source one msg call, no source account/key arguments or writable static. Runtime/allocator fail/div are abort prefixes under(an), no suffix or totality inferred.', 'cleanup':'Actual String Drop executes in root. Every per-label dealloc pointer/layout/content K087..102 has matched failure, cap18 or36 as derived. Existing allocator deallocation law plus NIJ_StringCleanup.account_frame/growth_frame on fresh private objects; allocator state changes retained, account/oracle projection preserved.'},source_association='NIJ_ERROR_ASSOCIATION.json and NIJ_error_check.py validate frozen whole root, actual reachable harness bodies, all eight labels/features, exact KMX and metadata cut, paired controls, actual cleanup and standard ax2/NFX. NIJ_ErrorJoin bytes/source/exhaustive/abort_prefix joins the adopted NGL_ErrorModel full Result/state representation. No extracted generic std body or new extraction claimed.',effects='Exactly one chronological log on returning paths, exact per-label bytes and InvalidInstructionData. Actual private String allocation/growth/drop; only its fresh allocation may be freed. Runtime/allocator abort prefixes have no later event; no discarded error effect or account/key mutation.',combined='NIJ_L029',audit=['NIJ_L030 raw25 new/headline roots; same optimized binary with eight fixtures from NIJ_L021; NFX exit0'],trust_reclassification='Existing P6/D188 option-A semantic transport, Std/allocator/compiler/runtime realization retained/reclassified. No new trust row or RuntimeCpiReadonlyEntry7.',root_model='AspisR1.RPx_Deployed.deployed; frozen3; L154 parameter')
c['semantic_review_sha256']=sha(json.dumps(c,sort_keys=True).encode());new=[]
obligations={
 'compiler_metadata':c['callee_laws']['compiler metadata'],
 'debug_String_writer':c['callee_laws']['Debug callback/String'],
 'String_growth_copy':'Exact KMX pointer copy/realloc patches and paired failures; actual String capacity/value/frame native packets; NIJ_ArgumentMetadata.message_bound and NHY_StringAppend contents.',
 'sol_log':c['callee_laws']['logging'],
 'String_drop_dealloc':c['callee_laws']['cleanup'],
 'ProgramError_constructor':'Actual frozen returns InvalidInstructionData on every returning path; full native roots and NIJ_ErrorJoin full Result/state map.'}
for rid in ['TX1:NGB001','TX2:211']:
 r=copy.deepcopy(by[rid]);assert r['composed_status']=='OPEN'
 assert not r.get('canonical_callees',[]) and not r.get('caller_domain_obligations',[])
 named=copy.deepcopy(r.get('named_hypotheses',[]))
 for h in named:
  assert h['name'] in ['NCS_R144.PacketDomain','NCS_R144.PhysicalInterpretation']
  h['discharged_by']='NIJ::error: '+('Complete deployed8-constructor domain, exact fixed literal Args metadata derived natively for each Error; actual String/syscall/Result cases with exhaustive NIJ_ErrorJoin table. No parent-success or output premise.' if h['name'].endswith('PacketDomain') else 'Exact frozen whole-function native packets, real String and cleanup, source/callback/callee-domain checks, same decoded eight Error/ProgramError constructor ports and byte-exact logger; NIJ_ErrorJoin source/full Result plus ax2/NFX. P6/D188 compiler/Std/allocator/runtime trust remains explicit option-A reclassification, not discharge of headline tool trust.')
 # Inventory error rows omitted macro/std callbacks. Add obligations explicitly,
 # including the newly inventoried TX1 occurrence; never treat omission as proof.
 r.update(named_hypotheses=named,open_transitive_dependencies=[],caller_domain_obligations=[dict(id='external:'+rid+':'+name,call=dict(name=name,expression='error:'+name,resolution='explicit macro/std/runtime boundary'),owner='Aspis S2 lead / NIJ entry error',required='Exact argument/domain/result/effect/frame law at this frozen returning/abort-prefix call',status='CLOSED',discharged_by='NIJ::error: '+why) for name,why in obligations.items()],composed_status='CLOSED',bridge_status='CLOSED-CONDITIONAL',selected_claims=['NIJ::error'],active_support_receipts=[str((E/x['positive']/'receipt.json').relative_to(R)) for x in a['instantiations']],composed_reason='Every deployed Debug/String instantiation, compiler metadata packet, actual whole root and runtime byte arguments, actual cleanup/deallocation argument/frame, coherent source/model and ax2/NFX. Explicit macro/std obligations added rather than omitted.')
 assert not n.row_checks(r,by[rid],c),n.row_checks(r,by[rid],c);n.certificate_checks(type('Support',(),{'support':lambda self,c:None})(),c)
 candidates[rid]=('NIJ',r);certs[rid]=c;new.append(r)
tiny=copy.deepcopy(base);tiny['rows']=[copy.deepcopy(by[rid]) for rid in candidates]
admitted=n.admit(tiny,candidates,certs,{'NIJ':['TX2:202','TX1:NGB001','TX2:211']});outby=dict(by);outby.update({r['row']:r for r in admitted['rows']})
assert all(outby[rid]['composed_status']=='CLOSED' for rid in candidates)
assert all(outby[rid]['composed_status']==by[rid]['composed_status'] for rid in by if rid not in candidates)
for row in new:
 bad=copy.deepcopy(row);bad['caller_domain_obligations'][0]['status']='OPEN';assert 'Open caller-domain obligation' in n.row_checks(bad,by[row['row']],c)
 bad=copy.deepcopy(row);bad['frozen_body_sha256']='0'*64;assert 'candidate frozen identity mismatch' in n.row_checks(bad,by[row['row']],c)
assert lzma.decompress(basepath.read_bytes())==data
counts={s:sum(r['composed_status']==s for r in outby.values()) for s in ['CLOSED','OPEN','QUALIFIED']}
put('NIJ_CLOSED.json',dict(schema_version=1,frozen_revision=base['frozen_revision'],new_composed_functions=2,new_composed_rows=3,functions=[priorc['functions'][0],c],driver_root_status='OPEN'))
rows=prior['rows']+new;put('NIJ_EDGES.json',dict(edges=[o for r in rows for o in r['caller_domain_obligations']],no_out_of_slice_credit=True))
delta=dict(prior,new_closed_rows=[r['row'] for r in rows],rows=rows,whole_ledger_counts_after_inherited_and_new=counts)
delta['checks_added']+=['explicit macro/std/cleanup obligations for both error inventory occurrences','all8 full actual String/error roots with matched controls and constant Parse stability','actual dealloc pointer/layout/contents and fresh-allocation cleanup frame','calibrated NoShortcut domain and wrong Some(corrupted) callee control','frozen source/body identity and each added callback/domain denial']
delta['mutation_denials']+=['error metadata boundary OPEN denied for each occurrence','error frozen identity mismatch denied for each occurrence']
put('NIJ_LEDGER_DELTA.json',delta)
put('NIJ_AUDIT.json',dict(status='PASS_AX2_NFX',combined=['NIJ_L018','NIJ_L029'],roots=read(E/'NIJ_stage1_audit/proof0.json')['results']+raw['results'],fixtures=fx,scan=scan,walker_sha256=read(E/'NIJ_WALKER_PIN.json')['sha256'],driver_diffs=['NIJ_ProofDriver.diff','NIJ_ScanDriver.diff'],standard_axioms_only=True,scope='Focused coherent cached replays, no cold release replay or ELF reproduction claim'))
put('NIJ_LOCAL_VALIDATION.json',dict(target='NIJ entry+error association and unchanged NFK row/certificate/admit with added strict callback gates',exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss//(1024 if sys.platform=='darwin' else 1),swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),source_sha256=sha(Path(__file__).read_bytes()),print_axioms='N/A Python, formal roots in NIJ_AUDIT.json',new_closed_rows=3))
print(json.dumps(dict(status='PASS',new_closed_rows=3,functions=2,counts=counts)))
