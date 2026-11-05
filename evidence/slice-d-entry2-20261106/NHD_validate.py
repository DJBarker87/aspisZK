"""Add-only, fail-closed review. Never writes predecessor evidence or admits a row."""
from pathlib import Path
import sys,json,lzma,hashlib,re,types,copy,collections,time,resource,subprocess
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;P=E.parent/'slice-d-entry-20261105';STANDARD={'propext','Classical.choice','Quot.sound'}
sha=lambda b:hashlib.sha256(b).hexdigest();J=lambda n:json.loads((E/n).read_text())
def put(n,x):(E/n).write_text(json.dumps(x,indent=1)+'\n')
def log(a):return lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
start=time.monotonic()
subprocess.run([sys.executable,str(E/'NHD_pack.py'),'--check'],check=True,capture_output=True)
subprocess.run([sys.executable,str(E/'NHD_expected_imports.py')],check=True,capture_output=True)
# Run predecessor validators unchanged; redirect only their output serialization.
raw=(P/'NGL_certify.py').read_bytes();m=types.ModuleType('NHD_retained_checks');m.__file__=str(P/'NGL_certify.py');exec(compile(raw,m.__file__,'exec'),m.__dict__)
m.put=lambda name,x:put('NHD_REUSED_'+name,x)
reuse=[m.native_review(),m.model_review(),m.source_review()]
receipts=[json.loads(l) for l in (E/'NHD_ATTEMPTS.jsonl').read_text().splitlines()];assert len({r['attempt'] for r in receipts})==len(receipts)
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for r in receipts:
 assert r['limits']==limits and int(r['swaps'])==0 and int(r['peak_rss_kib'])<8*1024*1024
 assert r['source_revision'] and 'wall_seconds' in r and 'print_axioms' in r
 ad=J(r['attempt']+'-admission.json');assert ad['exit']==0 and ad['reservation']['allowed'] is True
 if r['kind']=='kani':
  a=r['attempt'];assert J(a+'-graph-check.json')['graph_matches_frozen'] and J(a+'-erasure-check.json')['passed'] and not J(a+'-source-check.json')['errors']
  lock=J(a+'-lock-check.json');assert lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  assert 'pool-adapter,private-leaf-salts' in r['native_command'] and '--locked' not in r['native_command']
cal=J('NHD_CALIBRATION.json');assert len(cal['interfaces'])==3
for item in cal['interfaces']:
 assert item['status']=='OPEN' and 'Arbitrary' in log(item['stub_verified']) and 'VERIFICATION:- FAILED' not in log(item['stub_verified'])
 assert J(item['real_body']+'/receipt.json')['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in log(item['real_body'])
 assert 'assignable' in log(item['modifies']) and 'VERIFICATION:- FAILED' in log(item['modifies'])
# Existing NFK code is executed without alteration. Preserve the NGZ 599-row basis;
# missing legacy OPEN-row fields are not defaulted and no full-baseline admission is attempted.
n=m.NFK();basepath=E.parent/'ledger9-20261105/NGZ_LEDGER.json.xz';basebytes=lzma.decompress(basepath.read_bytes());base=json.loads(basebytes);assert len(base['rows'])==599
by={r['row']:r for r in base['rows']};counts=dict(collections.Counter(r['composed_status'] for r in base['rows']));assert counts=={'CLOSED':303,'OPEN':296}
missing=[r['row'] for r in base['rows'] if 'caller_domain_obligations' not in r];assert all(by[x]['composed_status']=='OPEN' for x in missing)
b=by['TX2:223'];fake=copy.deepcopy(b);fake['frozen_body_sha256']='0'*64
assert 'candidate frozen identity mismatch' in n.row_checks(fake,b,{'id':'not a certificate'})
try:n.certificate_checks(type('Support',(),{'support':lambda self,c:None})(),{'id':'bad','inner_hypotheses_remaining':['unexecutable calibration']})
except ValueError:pass
else:raise AssertionError('NFK accepted residual obligation')
# Additional admission predicate: an error exit alone is never a semantic negative.
def semantic_negative(s):return 'VERIFICATION:- FAILED' in s and 'Failed Checks:' in s and 'timed out' not in s and 'internal compiler error' not in s
for a in ['NHD_K004','NHD_K008','NHD_K012','NHD_K050','NHD_K053','NHD_K056','NHD_K034','NHD_K039','NHD_K045','NHD_K046','NHD_K047','NHD_K048']:assert not semantic_negative(log(a)),a
for a in ['NHD_K005','NHD_K009','NHD_K013','NHD_K051','NHD_K054','NHD_K057','NHD_K058','NHD_K059','NHD_K060']:assert semantic_negative(log(a)),a
old=J('NHD_audit/proof0.json');new=J('NHD_delta_audit/proof1.json');roots=old['results']+new['results'];assert len(roots)==14
for x in roots:assert x['equal'] and set(x['walked_axioms'])==set(x['collect_axioms'])<=STANDARD
fixture=J('NHD_audit/fixtures.json');assert fixture['same_optimized_binary_sha256']==old['same_optimized_binary_sha256']==new['same_optimized_binary_sha256']
assert len(fixture['results'])==8 and all(x['equal'] for x in fixture['results'])
assert all(len(x['walked_axioms'])==1 for x in fixture['results'][:4]) and all(not x['walked_axioms'] for x in fixture['results'][4:])
scan=[json.loads(l) for l in (E/'NHD_LOADED_scan.jsonl').read_text().splitlines()];assert all(x['imports_match'] and not x['dangling'] and not x['duplicate_owners'] for x in scan)
# Every final model body matches a successful focused compile; failed versions excluded.
focused=[]
for p in E.glob('NHD_*.lean'):
 if p.stem in ['NHD_ProofDriver','NHD_ScanDriver']:continue
 h=sha(p.read_bytes());matches=[r['attempt'] for r in receipts if r['kind']=='lean' and r['module']==p.stem and r['exit_status']==0 and h in r['source_hashes'].values()];assert matches,p.stem
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\s|set_option (maxHeartbeats|maxRecDepth)',p.read_text(),re.M)
 focused.append(dict(module=p.stem,source_sha256=h,successful_attempts=matches))
for p in E.glob('NEP_*_REACHABLE.txt.xz'):
 data=lzma.decompress(p.read_bytes());assert sha(data)==p.with_suffix('.sha256').read_text().split()[0]
put('NHD_AUDIT.json',dict(status='PASS_AX2_AND_NFX; NO_ADMISSIONS',headline='AspisR1.RPx_Deployed.deployed',combined_import='NHD_L017',raw_audits=['NHD_L014','NHD_L018'],roots=roots,raw_root_count=14,standard_axioms_only=True,fixtures=fixture,source_scan=dict(modules=len(scan),dangling=0,incompatible_owners=0,import_mismatches=0),focused_sources=focused,retained_NGL_validator_sha256=sha(raw),retained_NGL_checks=reuse,cohort='Focused cached NGK + NGL + NHD; not a cold final release replay'))
put('NHD_CLOSED.json',dict(schema_version=1,frozen_revision=base['frozen_revision'],new_composed_functions=0,new_composed_rows=0,functions=[],driver_root_status='OPEN'))
put('NHD_LEDGER_DELTA.json',dict(baseline=str(basepath),baseline_uncompressed_sha256=sha(basebytes),baseline_archive_sha256=sha(basepath.read_bytes()),new_closed_rows=[],rows=[],no_other_status_change=True,validator_checks_added_only=True,unchanged_NFK_validator_sha256=json.loads((P/'NGL_VALIDATOR_INPUT_PINS.json').read_text())['unchanged_NFK_validator']['sha256'],checks_added=['per-run frozen source/graph/lock/offline/features/caps','content-addressed exact input snapshots','exact-signature calibration classification; compile error is not semantic FAIL','timeout/ICE is not semantic FAIL','14 raw roots; same-binary eight fixtures; fresh NFX scan','current-source successful compile hashes','byte-exact baseline preservation with no defaults for incomplete OPEN rows'],whole_ledger_counts_after=dict(total=599,**counts),legacy_schema_incomplete_open_rows=missing,baseline_preserved_byte_exactly=True,admission_path='No proposed candidate is admissible; do not invoke old whole-ledger admission on schema-incomplete OPEN rows',mutation_denials=14,trust_reclassification='P6/D188 option A retained; no removal or new adoption'))
# Hash the tool-independent validation result itself; resource figures are local Python only.
summary=dict(status='PASS_FAIL_CLOSED',new_closed_rows=0,kani_runs=sum(r['kind']=='kani' for r in receipts),lean_compiles=sum(r['kind']=='lean' for r in receipts),support_scopes=sum(r['kind'] not in ['kani','lean','extract'] for r in receipts),extraction_runs=0,raw_roots=14,scan_modules=len(scan),baseline_counts=counts,wall_seconds=time.monotonic()-start,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss//(1024 if sys.platform=='darwin' else 1),swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),print_axioms='N/A: ordinary Python validation; proof axioms in NHD_AUDIT.json',source_sha256=sha(Path(__file__).read_bytes()))
put('NHD_VALIDATION.json',summary);print(json.dumps(summary))
