"""Additive NID validation; baseline graph/resource/feature checks retained."""
from pathlib import Path
import json,hashlib,lzma,re,sys,copy,subprocess,base64
E=Path(__file__).resolve().parent;ROOT=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
FROZEN=json.loads((ROOT/'evidence/extract-stage-20261106/NHR_STAGING_MANIFEST.json').read_text())['files']
def check(ad,rc,graph,lock):
 assert ad['exit']==0 and ad['reservation']['allowed'] is True,'admission'
 assert graph['graph_matches_frozen'] is True,'graph'
 assert graph['lock_sha256']==lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef' and lock['unchanged'] is True,'lock'
 argv=rc['command'];assert argv==['python3','NID_gate.py',rc['attempt']+'.json']
 x=json.loads((E/(rc['attempt']+'.json')).read_text())
 assert x['env']['CARGO_NET_OFFLINE']=='true'
 assert x['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert x['native_command'][x['native_command'].index('--harness-timeout')+1]=='90s'
 assert '--locked' not in x['native_command']
 assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},'limits'
 assert graph.get('all_crate_features'),'complete feature graph'
 f={r['name']:set(r['features']) for r in graph['all_crate_features']}
 assert f['aspis-r1-cost-probe']=={'default','private-leaf-salts','optimized-terminal','program-build'},'deployed library features'
 assert f['aspis-core']=={'r0'},'deployed core features'
 statement={'pool-v1-kernel','r0','spend-dynamic-rate512','pool-v1-pair-forest-active-mask-basis-audit','pool-v1-pair-forest-binary-copy-weights-audit','pool-v1-pair-forest-copy-finish-dot-basis-audit','pool-v1-pair-forest-copy-pattern-basis-audit','pool-v1-pair-forest-copy-selector-tensor-basis-audit','pool-v1-pair-forest-copy-tag-dot-basis-audit','pool-v1-pair-forest-endpoint-selector-cache-audit','pool-v1-pair-forest-packed-digest-audit','pool-v1-pair-forest-packed-digest-selector-tensor-audit','pool-v1-pair-forest-packed-range-audit','pool-v1-pair-forest-pattern-window-audit','pool-v1-pair-forest-semantic-factor-audit'}
 assert f['aspis-statement']==statement,'deployed statement features'
 assert '--features' in x['native_command'] and x['native_command'][x['native_command'].index('--features')+1]=='private-leaf-salts,optimized-terminal,program-build'
 for n,pin in json.loads((E/rc['attempt']/'sources/NID_SOURCE_PINS.json').read_text()).items():
  p=E/rc['attempt']/'sources/NID_src'/n
  if p.exists():assert sha(p)==pin,('source',n)
  else:
   # Frozen payload is committed once; every modified input must remain archived.
   assert n in FROZEN and FROZEN[n]['sha256']==pin,('missing modified source',n)
   pre=json.loads((E/(rc['attempt']+'-source-check.json')).read_text())
   assert pre['files']>=len(FROZEN) and pre['errors']==[],('pre-run source check',n)
 return True

def validate(final=True):
 receipts=[]
 for p in sorted(E.glob('NID_[KLE][0-9][0-9][0-9]/receipt.json')):
  r=json.loads(p.read_text());a=r['attempt'];receipts.append(r)
  ad=json.loads((E/(a+'-admission.json')).read_text())
  assert ad['exit']==0 and ad['reservation']['allowed'] is True,('admission',a)
  assert r['source_revision'] and r.get('wall_seconds') is not None and r.get('peak_rss_kib') is not None and str(r.get('swaps'))=='0'
  assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
  if r['kind']=='kani':check(ad,r,json.loads((E/(a+'-graph-check.json')).read_text()),json.loads((E/(a+'-lock-check.json')).read_text()))
  for n,h in r['source_hashes'].items():assert sha(E/a/'sources'/n)==h,(a,n)
 counts={k:sum(r['kind']==k for r in receipts) for k in ['kani','extract']};counts['lean_support']=len(receipts)-counts['kani']-counts['extract']
 assert counts['kani']<=120 and counts['extract']<=1 and counts['lean_support']<=80,counts
 for rel,pin in json.loads((E/'NID_INPUT_PINS.json').read_text()).items():assert sha(ROOT/rel)==pin['sha256'],rel
 manifest=ROOT/'evidence/extract-stage-20261106/NHR_STAGING_MANIFEST.json'
 raw=lzma.decompress((manifest.parent/'NHR_FROZEN_PAYLOAD.json.xz').read_bytes())
 assert hashlib.sha256(raw).hexdigest()==(manifest.parent/'NHR_FROZEN_PAYLOAD.json.sha256').read_text().strip()
 payload=json.loads(raw);assert set(payload)==set(FROZEN)
 for n,info in FROZEN.items():
  bs=base64.b64decode(payload[n],validate=True)
  assert hashlib.sha256(bs).hexdigest()==info['sha256'] and len(bs)==info['bytes'],n
 baseline=json.loads((E/'NID_BASELINE_BOUNDARIES.json').read_text())
 assert sha(ROOT/'evidence/ledger10-20261106/NHO_LEDGER.json.xz')==baseline['baseline_sha256']
 assert subprocess.run(['git','diff','--quiet','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','HEAD','--','crates','programs'],cwd=ROOT).returncode==0
 assert sha(ROOT/'evidence/kani-mitig-20261028/KMX_copy_stubs.patch')=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 for p in E.rglob('*'):
  if p.is_file():assert p.stat().st_size<=20*1024**2,('oversize',str(p))
 if final:
  assert json.loads((E/'NID_CLOSED.json').read_text())['new_composed_rows']==0
  delta=json.loads((E/'NID_LEDGER_DELTA.json').read_text());assert delta['row']=='TX2:065' and delta['after']=='OPEN' and delta['promotions']==[]
  native=json.loads((E/'NID_NATIVE_MATRIX.json').read_text())
  for fam in native['selected_families']:
   for key in ['positive','control','rename']:
    a=fam[key];rc=json.loads((E/a/'receipt.json').read_text());out=(E/a/'stdout.log').read_text()
    assert ('Checking harness '+rc['module']+'...') in out
    if key=='control':assert rc['exit_status']!=0 and 'VERIFICATION:- FAILED' in out and 'Failed Checks: assertion failed:' in out and 'NID_native.rs' in out
    else:assert rc['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in out
   srcs=[json.loads((E/a/'receipt.json').read_text())['source_hashes'] for a in [fam['positive'],fam['control'],fam['rename']]]
   # Source variants must be identical, except the explicitly recorded pre-control
   # reader-entry correction, whose non-control branch erasure is checked separately.
   if fam['name']!='reader_entry':assert srcs[0]==srcs[1]==srcs[2],fam['name']
   else:
    import runpy
    assert runpy.run_path(str(E/'NID_control_erasure.py'))['out']['status']=='PASS'
    assert srcs[1]==srcs[2]
   cmds=[json.loads((E/(fam[k]+'.json')).read_text()) for k in ['positive','control','rename']]
   assert ' --cfg NID_invert' not in cmds[0]['env']['RUSTFLAGS'] and ' --cfg NID_invert' in cmds[1]['env']['RUSTFLAGS'] and ' --cfg NID_invert' not in cmds[2]['env']['RUSTFLAGS']
  for pair in native['selected_pairs']:
   a,b=pair['positive'],pair['control'];ra=json.loads((E/a/'receipt.json').read_text());rb=json.loads((E/b/'receipt.json').read_text())
   assert ra['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in (E/a/'stdout.log').read_text()
   assert rb['exit_status']!=0 and 'Failed Checks: assertion failed:' in (E/b/'stdout.log').read_text() and 'VERIFICATION:- FAILED' in (E/b/'stdout.log').read_text()
   assert ra['source_hashes']==rb['source_hashes']
  audit=json.loads((E/'NID_AUDIT.json').read_text());assert audit['status']=='PASS'
  expected={n for g in json.loads((E/'NID_AUDIT_ROOTS.json').read_text())['groups'] for n in g}
  assert {r['root'] for r in audit['roots']}==expected
  for r in audit['roots']:assert r['equal'] is True and set(r['walked_axioms'])==set(r['collect_axioms']) and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}
  scan=[json.loads(l) for l in (E/'NID_LOADED_scan.jsonl').read_text().splitlines()]
  assert all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in scan)
  fixture=json.loads((E/'NID_audit/fixtures/fixtures.json').read_text());assert fixture['exit_status']==0 and len(fixture['results'])==8
  for n in ['NID_CACHE_VERIFICATION.json','NID_SOURCE_VERIFICATION.json']:assert json.loads((E/n).read_text())['status']=='PASS'
  assert 'CBMC timed out' in (E/'NID_K062/stdout.log').read_text()
  assert audit['walker_byte_identical'] is True
 return dict(status='PASS' if final else 'PREFLIGHT_ONLY',counts=counts,receipts=len(receipts),promotions=0,baseline_checks='unchanged graph/resource/features plus stricter full frozen source pins; zero promotion while any slot open')
if __name__=='__main__':
 final='--preflight' not in sys.argv;out=validate(final)
 (E/('NID_VALIDATION.json' if final else 'NID_PREFLIGHT.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
