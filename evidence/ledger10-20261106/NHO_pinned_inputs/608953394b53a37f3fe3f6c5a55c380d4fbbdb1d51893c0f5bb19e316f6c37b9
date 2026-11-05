"""Additive admission checks. OPEN stays OPEN; no historical gate is waived."""
from pathlib import Path
import json,hashlib,subprocess,re,copy,collections
from NGU_io import E,raw,text,read

def require_caps(receipt,admission):
 assert admission['exit']==0 and admission['reservation']['allowed'] is True
 assert receipt['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert int(receipt['swaps'])==0

def require_scan(s):
 assert s['dangling']==s['incompatible_owners']==s['import_mismatches']==0

def require_raw(rows):
 assert all(r['equal'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in rows)

def require_delta(d):
 assert d['added_checks_only'] and d['all_other_rows_unchanged'] and not d['new_closed_rows']
 assert not d['security_target_established'] and not d['cold_release_replay']
 assert len(d['rows'])==1 and d['rows'][0]['row']=='TX1:193'
 r=d['rows'][0];assert r['before']==r['after']=='OPEN'
 assert len(r['remaining_hypotheses'])==5 and all(x['status'].startswith('OPEN') or x['status'].startswith('caller') for x in r['remaining_hypotheses'])

def validate():
 attempts=[json.loads(l) for l in text(E/'NGU_ATTEMPTS.jsonl').splitlines()]
 assert len({r['attempt'] for r in attempts})==121
 assert sum(r['kind']=='kani' for r in attempts)==40
 assert sum(r['kind'] not in ['kani','extract'] for r in attempts)==80
 assert sum(r['kind']=='extract' for r in attempts)==1
 assoc={r['attempt']:r for r in read(E/'NGU_REVISION_ASSOCIATION.json')}
 for row in attempts:
  a=row['attempt'];r=read(E/a/'receipt.json');cfg=read(E/(a+'.json'))
  require_caps(r,read(E/(a+'-admission.json')))
  assert r['command'] and r['wall_seconds']>=0 and r['peak_rss_kib'] and r['print_axioms'] is not None
  assert cfg.get('source_revision') or a in assoc
  assert r['deps_fingerprint']['selected_objects']
  assert any('/Aeneas/' in p for p in r['deps_fingerprint']['selected_objects'])
  for n,h in r['source_hashes'].items():assert hashlib.sha256(raw(E/a/'sources'/n)).hexdigest()==h,(a,n)
  if r['kind']=='kani' and a not in ['NGU_K001','NGU_K029']:
   g=read(E/(a+'-graph-check.json'));lock=read(E/(a+'-lock-check.json'))
   assert g['graph_matches_frozen'] and not g['new_package_tuples'] and not g['edge_errors']
   assert lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
   features=read(E/(a+'-all-crate-features.json'));assert len(features)>400
   assert cfg['env']['CARGO_NET_OFFLINE']=='true' and '-Copt-level=3' in cfg['env']['RUSTFLAGS']
   assert cfg['native_command'][cfg['native_command'].index('--features')+1]=='private-leaf-salts,optimized-terminal,program-build'
   source=text(E/a/'sources/NGU_src/crates/aspis-r1-cost-probe/src/NGU_stages.rs')
   assert not re.search(r'\bstatic\s+mut\b|Option\s*<\s*fn|proof_for_contract|stub_verified',source)
   assert not re.search(r'\.mul\s*\(',source),'field multiplication in native harness'
 # Every accepted final module is exactly its successful compiled source.
 for p in E.glob('NGU_*.lean'):
  matches=[r for r in attempts if r['kind']=='lean' and r['module']==p.stem and r['exit_status']==0]
  assert matches,p
  r=matches[-1];assert hashlib.sha256(p.read_bytes()).hexdigest()==read(E/r['attempt']/'receipt.json')['source_hashes']['NGU_generated/'+p.name],p
  assert not re.search(r'\b(sorry|admit|axiom|native_decide|XRn_Join\w*|XRy_ArrayRead)\b',p.read_text()),p
  assert not re.search(r'set_option (maxRecDepth|maxHeartbeats)',p.read_text()),p
 subprocess.run(['python3',str(E/'NGU_generate.py'),'--check'],stdout=subprocess.DEVNULL,check=True)
 require_scan(read(E/'NGU_SCAN.json'));require_delta(read(E/'NGU_LEDGER_DELTA.json'))
 roots=[]
 for i in range(26):roots+=read(E/f'NGU_audit/batch{i}/proof{i}.json')['results']
 require_raw(roots);assert len(roots)==367
 manifest=read(E/'NGU_AUDIT_ROOTS.json');assert collections.Counter(r['root'] for r in roots)==collections.Counter(n for g in manifest['groups'] for n in g)
 assert read(E/'NGU_AUDIT.json')['checked_statement_owners']==366
 assert read(E/'NGU_WALKER_CONFORMANCE.json')['byte_identical']
 fixture_pin=read(E/'NGU_L040/NGU_ProofDriver_BINARY_PIN.json')
 for row in attempts:
  if row['kind']=='audit' and row['exit_status']==0:
   assert read(E/row['attempt']/'NGU_ProofDriver_BINARY_PIN.json')==fixture_pin
 extraction=read(E/'NGU_EXTRACTION_STATUS.json');assert extraction['charon_exit']==0 and extraction['aeneas_exit']==2 and not extraction['admitted'] and not extraction['raw_lean_outputs']
 assert extraction['lock_unchanged'] and not extraction['canonical_packet_changed']
 assert read(E/'NGU_HOST_END.json')['source_wrapper_restored'] and read(E/'NGU_HOST_END.json')['no_active_owned_provers']
 import lzma
 closure=lzma.decompress(raw(E/'NGU_CLOSURE_PINS.json.xz'));assert hashlib.sha256(closure).hexdigest()==text(E/'NGU_CLOSURE_PINS.json.sha256').strip()
 assert len(json.loads(closure)['selected_objects'])==30048

 assert read(E/'NGU_NATIVE_MATRIX.json')['matched_families']==17
 assert read(E/'NGU_CLOSED.json')['composed_status']=='OPEN'
 assert hashlib.sha256((E/'NGU_KMX.patch').read_bytes()).hexdigest()=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 # All task source/config fields in crates/programs stay frozen. No ELF trigger.
 assert not subprocess.check_output(['git','diff','--name-only','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','HEAD','--','crates','programs'],text=True)
 assert not subprocess.check_output(['git','diff','--name-only','HEAD','--','crates','programs'],text=True)
 assert not any(p.stat().st_size>20*1024*1024 for p in E.rglob('*') if p.is_file())
 assert not list(E.rglob('__pycache__'))
 assert not any(p.name.endswith(('.tar','.tar.xz','.tgz','.olean','.elf')) for p in E.rglob('*') if p.is_file())
 for p in E.rglob('*.ref.json'):raw(Path(str(p)[:-9]))
 return dict(passed=True,attempts=len(attempts),new_closed_rows=[],checks='Caps/admission, source snapshots, frozen offline graph/lock, features, no native field product/static/Optionfn, exact compiled sources, deterministic proof generation, raw axioms, fixtures, statement owners, coherence, frozen shipped source, no closure promotion, all evidence input refs')

if __name__=='__main__':
 # Prevent bytecode creation during validation, before checking hygiene.
 import sys;sys.dont_write_bytecode=True
 result=validate();(E/'NGU_VALIDATION.json').write_text(json.dumps(result,indent=1)+'\n');print(json.dumps(result))
