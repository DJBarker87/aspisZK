"""Own proof/evidence validation; never launches a prover or changes shared tools."""
from pathlib import Path
import json,subprocess,hashlib,re
E=Path(__file__).resolve().parent
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
BASE='3e94938e0a^'
def sha(data):return hashlib.sha256(data).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],text=True).strip()
accepted={'NBH_Frontier':'NBH_L004','NBH_LiveFrontier':'NBH_L005','NBH_Validators':'NBH_L007','NBH_ArrayEq':'NBH_L014','NBH_LiveValidator':'NBH_L015','NBH_NativeFrontier':'NBH_L016','NBH_NativeLiveFrontier':'NBH_L017','NBH_FrontierTrace':'NBH_L018','NBH_Exact':'NBH_L021','NBH_Audit':'NBH_L022'}
modules={}
for name,a in accepted.items():
 p=Path('lean')/(name+'.lean');r=json.loads((E/a/'receipt.json').read_text());h=sha(p.read_bytes())
 assert r['exit_status']==0 and h in r['source_hashes'].values(),name
 assert r['print_axioms'] and all('sorryAx' not in line and 'axioms: [' in line for line in r['print_axioms'])
 for line in r['print_axioms']:
  ax=line.split('axioms: [',1)[1].split(']',1)[0]
  assert set(filter(None,ax.split(', ')))<={'propext','Classical.choice','Quot.sound'},line
 assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats)',p.read_text())
 assert 'XRn_' not in p.read_text()
 modules[name]={'attempt':a,'sha256':h,'receipt':str(E/a/'receipt.json'),'axioms':r['print_axioms']}
receipts={}
for p in sorted(E.glob('NBH_[LKG]*/receipt.json')):
 r=json.loads(p.read_text());assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert str(r['swaps'])=='0'
 target=r['command'][r['command'].index('--harness')+1] if r['kind']=='kani' else r['module']
 receipts[r['attempt']]={**r,'exact_target':target}
 if r['kind']=='kani':
  q=json.loads((E/(r['attempt']+'-graph.json')).read_text())
  assert q['graph_matches_frozen'] and q['lock_unchanged']
  assert q['lock_before_sha256']==q['lock_after_sha256']==q['frozen_lock_sha256']==sha(subprocess.check_output(['git','show',REV+':Cargo.lock']))
  assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  assert '--locked' not in r['command']
  if r['exit_status']==0:
   log=(p.parent/'stdout.log').read_text();assert 'VERIFICATION:- SUCCESSFUL' in log and '0 failures, 1 total' in log
 if r['kind']=='lean':
  assert all(sha((p.parent/'sources'/s).read_bytes())==h for s,h in r['source_hashes'].items())
# Historical native files are retained in serial source-sync payloads.
known={}
def know(path,data):known.setdefault('NBH_src/'+path,set()).add(sha(data.encode() if isinstance(data,str) else data))
know('Cargo.lock',subprocess.check_output(['git','show',REV+':Cargo.lock']))
for p in E.glob('NBH_SYNC*-payload.json'):
 x=json.loads(p.read_text())
 for path,data in x['files'].items():
  know(path,data)
  # K001's only correction was this nested-child constant path (before a solver).
  if path.endswith('NBH_after.rs'):know(path,data.replace('crate::pool_v1::POOL_V1_PAIR_CAPACITY','super::POOL_V1_PAIR_CAPACITY'))
 for path,v in x['parents'].items():
  frozen=subprocess.check_output(['git','show',REV+':'+path]).decode()
  assert v['original']==frozen
  know(path,frozen);know(path,frozen+v['marker'])
for a,r in receipts.items():
 if r['kind'] in ['kani','metadata']:
  for path,h in r['source_hashes'].items():assert h in known.get(path,set()),(a,path,h)
# Final modules are identical to their accepted source snapshots; no source rewrite
# was done to the NBD predecessor or any other prefix.
changes=set(git('diff','--name-only',BASE,'HEAD').splitlines())|set(git('diff','--name-only','HEAD').splitlines())
assert all(p.startswith('evidence/native-tx2d-20261027/') or p.startswith('lean/NBH_') for p in changes),changes
source_trees={}
for n in ['crates','programs']:
 a=git('rev-parse','HEAD:'+n);b=git('rev-parse',REV+':'+n);assert a==b
 assert not git('diff','HEAD','--',n)
 assert not git('ls-files','--others','--exclude-standard','--',n)
 source_trees[n]={'current':a,'frozen':b,'identical':True}
# Pin all48 member bodies without rewriting the inherited inventory.
inv=json.loads(Path('evidence/native-tx2b-20261027/NBD_MEMBERS.json').read_text())
files={}
for m in inv['members']:
 f=m['file']
 if f not in files:files[f]=subprocess.check_output(['git','show',REV+':'+f])
 data=files[f];assert sha(data)==m['file_sha256']
 assert sha(data[m['body_start_byte']:m['body_end_byte']])==m['body_sha256'],m['id']
# Reproduce the complete static helper caller-domain inventory.
s=files['crates/aspis-statement/src/pool_v1/pair_terminal.rs'].decode()
b=s.split('pub fn decode_pool_v1_pair_verified_afterstate_v1(',1)[1].split('\nfn exact<',1)[0]
ranges=[{'start':int(a),'stop':int(z),'width':int(z)-int(a)} for a,z in re.findall(r'exact\(&bytes\[(\d+)\.\.(\d+)\]\)',b)]
assert len(ranges)==22 and {r['width'] for r in ranges}=={8,32}
assert all(0<=r['start']<=r['stop']<=688 and r['width']<=64 for r in ranges)
assert ranges==json.loads((E/'NBH_ExactCallerDomains.json').read_text())['ranges']
summary={'status':'U03/U04/U05 OPEN; eight reached local bridges CLOSED, including five inherited;40 members OPEN','lean_used':sum(r['kind']=='lean' for r in receipts.values()),'lean_budget':100,'kani_used':sum(r['kind']=='kani' for r in receipts.values()),'kani_budget':30,'metadata_used':sum(r['kind']=='metadata' for r in receipts.values()),'lean_passed':sum(r['kind']=='lean' and r['exit_status']==0 for r in receipts.values()),'kani_passed':sum(r['kind']=='kani' and r['exit_status']==0 for r in receipts.values()),'modules':modules,'source_trees':source_trees,'member_bodies_pinned':len(inv['members']),'headline_premises_removed':0,'assumptions_changed':0,'source_to_ELF':'Retained L188 obligation; no shipped source change and no rebuild trigger. ELF pins inherited, not reproduced.'}
assert summary['lean_used']<=100 and summary['kani_used']<=30
if (E/'NBH_CACHE_END.json').exists():
 start=json.loads((E/'NBH_CACHE_START.json').read_text());end=json.loads((E/'NBH_CACHE_END.json').read_text())
 summary.update(cache_start_files=len(start),cache_end_files=len(end),cache_changed_existing=[p for p in start if p in end and start[p]!=end[p]],cache_missing_start=sorted(set(start)-set(end)))
 assert not summary['cache_missing_start']
 assert not [p for p in summary['cache_changed_existing'] if Path(p).name.startswith('NBH_')]
if (E/'NBH_RESOLVED_LIBRARY_PIN.json').exists():
 assert json.loads((E/'NBH_RESOLVED_LIBRARY_PIN.json').read_text())['all_resolved_objects_match_pinned_library']
 summary['actual_Aeneas_resolution_pinned']=True
if (E/'NBH_HOST_CLEANUP.json').exists():
 q=json.loads((E/'NBH_HOST_CLEANUP.json').read_text())
 assert not q['own_live_provers'] and q['persistent_cache_retained'] and q['library_pins_unchanged']
 summary['host_terminal_cleanup_verified']=True
if (E/'NBH_NBD_OBJECT_PINS.json').exists():
 assert all(x['matches'] for x in json.loads((E/'NBH_NBD_OBJECT_PINS.json').read_text()).values())
 summary['inherited_NBD_objects_match_handoff']=True
(E/'NBH_ATTEMPTS.jsonl').write_text(''.join(json.dumps({'attempt':a,**r})+'\n' for a,r in sorted(receipts.items())))
(E/'NBH_VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:summary[k] for k in ['status','lean_used','kani_used','metadata_used','lean_passed','kani_passed']}))
