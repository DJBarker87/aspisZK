"""Owned raw-gate validation. Raw checked declarations, never cached axiom summaries, decide the axiom set."""
from pathlib import Path
import sys,subprocess,json,time,lzma,hashlib,os
B=Path.cwd();mode=sys.argv[1];attempt=sys.argv[2];out=B/attempt;out.mkdir(exist_ok=True)
standard={'propext','Classical.choice','Quot.sound'}
start=time.monotonic();r=subprocess.run(['NND_native/NND_ProofDriver',mode],text=True,capture_output=True)
print(r.stdout,end='');print(r.stderr,end='',file=sys.stderr)
rows=[json.loads(l[len('NEP_RESULT '):]) for l in r.stdout.splitlines() if l.startswith('NEP_RESULT ')]
assert 'NEP_FAILURE ' not in r.stdout and r.returncode in [0,1],(r.returncode,'raw traversal failure')
exceptions=[l for l in r.stdout.splitlines() if l.startswith('NND_AUDIT_EXCEPTION ')]
if mode=='planted':
 expected=['NEP_Planted.matcher','NEP_Planted.viaPrivate','NEP_Planted.proof','NEP_Planted.viaAux']
 nonstandard=['NEP_Planted.matchAx','NEP_Planted.privateAx','NEP_Planted.proofAx','NEP_Planted.auxAx']
elif mode=='mutations':
 expected=['NEP_MutateMatch.matcher','NEP_MutatePrivate.viaPrivate','NEP_MutateProof.proof','NEP_MutateAux.viaAux']
 nonstandard=[None]*4
else:
 expected=json.loads((B/'NND_AUDIT_ROOTS.json').read_text())['groups'][int(mode[5:])]
 nonstandard=[None]*len(expected)
assert [x['root'] for x in rows]==expected,'Missing, duplicate, reordered or foreign root'
for x,ax in zip(rows,nonstandard):
 assert set(x['walked_axioms'])-standard==({ax} if ax else set()),x
 assert x['reachable_constants']>0 and x['edges_scanned']>0,x
mismatches=[x for x in rows if not x['equal']]
assert len(exceptions)==len(mismatches) and all('raw graph disagrees with collectAxioms' in x for x in exceptions),exceptions
assert (r.returncode==1)==bool(exceptions),'Unexplained native exit'
archives=[]
for p in sorted((B/'NND_audit').glob('NND_'+mode+'_*_REACHABLE.txt')):
 raw=p.read_bytes();z=p.with_suffix(p.suffix+'.xz');z.write_bytes(lzma.compress(raw))
 archives.append({'path':str(z.relative_to(B)),'sha256':hashlib.sha256(raw).hexdigest(),'archive_sha256':hashlib.sha256(z.read_bytes()).hexdigest(),'bytes':len(raw)})
assert len(archives)==len(expected)
summary={'mode':mode,'native_exit_status':r.returncode,'wall_seconds':time.monotonic()-start,'roots':rows,'cache_disagreements':mismatches,'archives':archives,'gate':'RAW_STANDARD_ONLY' if mode.startswith('proof') else 'FIDELITY_CONTROL_AS_EXPECTED'}
(out/'NND_RAW_AUDIT.json').write_text(json.dumps(summary,indent=1)+'\n')
print(json.dumps({'mode':mode,'raw_roots':len(rows),'native_exit':r.returncode,'cache_disagreements':len(mismatches),'validation':'PASS'}),flush=True)
if mode=='proof31':
 # Exact combined import closure, private objects included; no old-root proof audit.
 q=subprocess.run(['NND_native/NND_ProofDriver','closure'],text=True,capture_output=True)
 print(q.stdout,end='');assert q.returncode==0,q.stderr
 roots=os.environ['LEAN_PATH'].split(':');selected={}
 for module in json.loads((B/'NND_CLOSURE_MODULES.json').read_text()):
  rel=module.replace('.','/')+'.olean'
  p=next((Path(root)/rel for root in roots if (Path(root)/rel).is_file()),None)
  if p is None:
   sysroot=Path(os.environ['LEAN_SYSROOT'])/'lib/lean';p=sysroot/rel
  assert p.is_file(),module
  for f in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
   if f.is_file():
    h=hashlib.sha256()
    with f.open('rb') as stream:
     for block in iter(lambda:stream.read(1024*1024),b''):h.update(block)
    selected[str(f)]={'sha256':h.hexdigest(),'bytes':f.stat().st_size}
 (out/'NND_CLOSURE_PINS.json').write_text(json.dumps({'modules':json.loads((B/'NND_CLOSURE_MODULES.json').read_text()),'objects':selected,'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip() if (B/'.git').exists() else 'source revision in enclosing receipt'},indent=1)+'\n')
 print(json.dumps({'combined_closure_objects':len(selected),'validation':'PINNED'}),flush=True)
