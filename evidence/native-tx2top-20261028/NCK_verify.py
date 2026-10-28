"""Own final receipt/source and policy audit; does not invoke a prover."""
from pathlib import Path
import json,hashlib,re,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1]
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('NCK_[KL][0-9][0-9][0-9]/receipt.json'))]
leans=[r for r in receipts if r['kind']=='lean'];kanis=[r for r in receipts if r['kind']=='kani']
assert len(leans)<=80 and len(kanis)<=50
latest={}
for r in leans:latest[r['module']]=r
sources={}
for p in sorted((R/'lean').glob('NCK_*.lean')):
 r=latest.get(p.stem);h=hashlib.sha256(p.read_bytes()).hexdigest()
 assert r and r['exit_status']==0,(p.name,'no current passing receipt')
 assert h in r['source_hashes'].values(),(p.name,'current source hash mismatch')
 axioms=r['print_axioms'];assert all('sorryAx' not in l and 'axiom' in l for l in axioms)
 for line in axioms:
  if 'depends on axioms:' in line:
   a=line.split('depends on axioms:')[1].strip().strip('[]')
   assert set(a.split(', '))<={'propext','Classical.choice','Quot.sound'},line
 assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b|set_option (maxRecDepth|maxHeartbeats)',p.read_text()),p
 sources[p.name]=dict(sha256=h,attempt=r['attempt'],axioms=axioms)
for r in receipts:
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},r['attempt']
 if r['kind']=='kani':
  a=r['attempt'];before=(E/(a+'-lock-before.log')).read_text().strip();after=(E/(a+'-lock-after.log')).read_text().strip()
  assert before==after=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  graph=json.loads((E/(a+'-graph-check.json')).read_text());assert graph['graph_matches_frozen']
  assert any(p['sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67' for p in r['deps_fingerprint']['cfg_patch_chain'])
  assert '--locked' not in r['command']
large=[str(p) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024];assert not large,large
out=dict(lean_attempts=len(leans),kani_runs=len(kanis),lean_passes=sum(r['exit_status']==0 for r in leans),current_sources=sources,
 source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
 resources='all attempts individually capped; L017/L018 overlap excluded from one-scope compliance claim; see NCK_SEQUENCE_FINDING.json',
 scope='focused conditional model and finite native gates only; no frozen manifest or source-to-ELF replay')
(E/'NCK_VERIFICATION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k] for k in ['lean_attempts','kani_runs','lean_passes']}))
