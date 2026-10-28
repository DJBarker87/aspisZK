from pathlib import Path
import re,json,hashlib,subprocess,tempfile
E=Path(__file__).resolve().parent;L=Path('lean');sha=lambda b:hashlib.sha256(b).hexdigest()
rows=[json.loads(l) for l in (E/'NCX_ATTEMPTS.jsonl').read_text().splitlines()]
assert len({r['attempt'] for r in rows})==len(rows)
assert sum(r['kind']=='kani' for r in rows)==40
assert sum(r['kind']=='lean' for r in rows)<=60
for r in rows:
 a=r['attempt'];assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
 assert int(r['swaps'])==0,a
 admissions=list(E.glob(a+'-admission-*.json'));assert admissions,a
 assert any((x:=json.loads(p.read_text()))['exit']==0 and x['reservation']['allowed'] is True for p in admissions),a
 if r['kind']=='kani':
  g=json.loads((E/(a+'-graph.json')).read_text());assert g['graph_matches_frozen'] and g['lock_unchanged'] and g['offline'],a
  assert g['lock_before_sha256']==g['lock_after_sha256']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef',a
  assert g['KMX_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',a
  byname={g['packages'][p]['name']:v for p,v in g['features'].items()}
  assert set(byname['aspis-r1-cost-probe'])=={'default','optimized-terminal','private-leaf-salts','program-build'},a
  assert {'pool-adapter','private-leaf-salts'} <= set(byname['aspis-r1-cost-probe-program']),a
  assert {'r0','pool-v1-kernel'} <= set(byname['aspis-statement']),a
  assert sum(f.startswith('pool-v1-pair-forest-') for f in byname['aspis-statement'])==12,a
  assert 'Checking harness '+r['module']+'...' in (E/a/'stdout.log').read_text(),a
  assert (E/a/'sources/NCX_harness.patch').exists(),a
 else:
  for name,h in r['source_hashes'].items():
   p=E/a/'sources'/name
   if p.exists():assert sha(p.read_bytes())==h,(a,name)
# Reconstruct every native snapshot from frozen source + the committed per-run patch.
orig={};native=[]
for r in rows:
 if r['kind']!='kani':continue
 patch=E/r['attempt']/'sources/NCX_harness.patch'
 with tempfile.TemporaryDirectory(prefix='NCX_patch_',dir=E) as td:
  root=Path(td)
  for line in patch.read_text().splitlines():
   if line.startswith('+++ b/'):(root/line[6:]).parent.mkdir(parents=True,exist_ok=True)
   if line.startswith('--- a/'):
    name=line[6:]
    if name not in orig:orig[name]=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+name])
    p=root/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(orig[name])
  p=subprocess.run(['patch','-p1','--batch','-i',str(patch.resolve())],cwd=root,capture_output=True,text=True);assert p.returncode==0,(r['attempt'],p.stdout+p.stderr)
  for name,h in r['source_hashes'].items():
   if name.startswith('NCX_src/') and name!='NCX_src/Cargo.lock':assert sha((root/name[len('NCX_src/'):]).read_bytes())==h,(r['attempt'],name)
 native.append(r['attempt'])
# All canonical new Lean modules must match a successful exact-source receipt.
delivery={}
for p in sorted(L.glob('NCX_*.lean'))+sorted((L/'NCX_Reference').glob('*.lean')):
 h=sha(p.read_bytes());matches=[]
 for r in rows:
  if r['kind']=='lean' and r['exit_status']==0 and h in r['source_hashes'].values():matches.append(r['attempt'])
 assert matches,(str(p),'no passing current-source receipt')
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option (maxRecDepth|maxHeartbeats)',p.read_text()) or p.parent.name=='NCX_Reference',p
 delivery[str(p)]=dict(sha256=h,accepted_attempts=matches)
# Audit roots contain every new theorem, with only standard axioms.
targets=json.loads((E/'NCX_AUDIT_TARGETS.json').read_text());audits={}
for a in ['NCX_L041','NCX_L042']:
 r=next(r for r in rows if r['attempt']==a);assert r['exit_status']==0,a
 for line in r['print_axioms']:
  assert 'sorryAx' not in line,line
  name=re.search("'([^']+)'",line)[1]
  axioms=re.search(r'axioms: \[([^\]]*)\]',line)
  if axioms:assert set(x.strip() for x in axioms[1].split(',') if x.strip()) <= {'propext','Classical.choice','Quot.sound'},line
  audits[name]=line
for name in targets['theorems']+targets['configuration_theorems']+targets['definitions']:assert name in audits,name
native_rows=[r for r in rows if r['kind']=='kani'];timeouts=[r['attempt'] for r in native_rows if 'CBMC timed out' in (E/r['attempt']/'stdout.log').read_text()]
freeze=subprocess.run(['git','diff','--name-only','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','HEAD','--','Cargo.toml','Cargo.lock','crates','programs'],capture_output=True,text=True);assert freeze.returncode==0 and not freeze.stdout,freeze.stdout
assert not list(E.rglob('*.olean')) and not list(E.rglob('*.elf'))
large=[str(p) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024];assert not large,large
x=dict(counts={k:sum(r['kind']==k for r in rows) for k in ['kani','lean','extract']},kani=dict(pass_count=sum(r['exit_status']==0 for r in native_rows),timeouts=timeouts,intended_failures=[r['attempt'] for r in native_rows if r['exit_status']!=0 and r['attempt'] not in timeouts]),current_modules=delivery,audits=audits,patch_reconstruction_verified=native,frozen_shipped_files_unchanged=True,large_files=large,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
(E/'NCX_VALIDATION.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(dict(counts=x['counts'],current_modules=len(delivery),audit_lines=len(audits),all_native_patches_reconstructed=len(native))))
