#!/usr/bin/env python3
"""Source-only evidence consistency; does not claim release replay."""
from pathlib import Path
import hashlib,json,re,subprocess,tempfile
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
with tempfile.TemporaryDirectory(prefix='s126-packet-check-') as d:
 i=Path(d)/'in';o=Path(d)/'out';i.mkdir()
 for p in (E/'host/caller-v4/generated/AspisR1CurrentCaller').glob('*.lean.txt'):
  (i/p.name[:-4]).write_bytes(p.read_bytes())
 subprocess.run(['python3',str(R/'tools/s126-sdk-20261021/adapt-caller.py'),str(i),str(o)],check=True,capture_output=True)
 for p in o.iterdir():assert p.read_bytes()==(S/p.name).read_bytes(),p.name
owned=E/'modular-host/sources/owned-tail-v8/generated/AspisS2OwnedStage1'
if owned.exists():
 with tempfile.TemporaryDirectory(prefix='s126-owned-check-') as d:
  i=Path(d)/'in';o=Path(d)/'out';i.mkdir()
  for p in owned.glob('*.lean.txt'):(i/p.name[:-4]).write_bytes(p.read_bytes())
  subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/adapt-owned-tail.py'),str(i),str(o)],check=True,capture_output=True)
  for p in o.iterdir():assert p.read_bytes()==(S/p.name).read_bytes(),p.name
freeze=json.loads((E/'extraction-source-freeze.json').read_text())
assert all(r['matches'] and r['frozen_sha256']==r['extraction_workspace_sha256'] for r in freeze['files'])
receipts=[(p,json.loads(p.read_text())) for p in E.glob('*/receipt.json')]
accepted={}
for src in S.glob('*.lean'):
 text=src.read_text()
 assert not re.search(r'\bsorry\b|\bnative_decide\b|^axiom\s|set_option\s+(maxRecDepth|maxHeartbeats)',text,re.M),src
 rows=[(p,r) for p,r in receipts if r['target']==src.stem and r['exit_status']==0 and r['source_sha256']==sha(src)]
 assert rows,'no successful receipt for current source: '+src.name
 # Prefer the live focused object, if present; otherwise preserve historical receipt.
 obj=Path('/tmp/s126-current-caller-20261021-objects')/(src.stem+'.olean')
 if obj.exists():rows=[(p,r) for p,r in rows if r.get('object_sha256')==sha(obj)]
 assert rows,'current cached object lacks matching receipt: '+src.name
 def current_own_imports(row):
  for imported,pin in row.get('direct_imports',{}).items():
   own=Path('/tmp/s126-current-caller-20261021-objects')/(imported.replace('.','/')+'.olean')
   if own.is_file() and Path(pin['path'])==own and sha(own)!=pin['sha256']:return False
  return True
 rows=[(p,r) for p,r in rows if current_own_imports(r)]
 assert rows,('no receipt with current own direct imports',src.name)
 p,r=rows[-1]
 assert r['print_axioms'] and not any('sorryAx' in a or 'Formatter' in a for a in r['print_axioms']),p
 assert r['swaps']==0,p
 assert '-j1' in r['command'] and '-M4400' in r['command'],p
 accepted[src.stem]=dict(receipt=str(p.relative_to(E)),source_sha256=sha(src),wall_seconds=r['wall_seconds'],peak_rss_bytes=r['peak_rss_bytes'],swaps=r['swaps'],print_axioms=r['print_axioms'])
for p in E.rglob('*'):
 if p.is_file():assert p.suffix not in ['.olean','.o','.a','.so','.dylib','.llbc','.bc'],p
# Check suffix was copied in full, including nested Break arms.
s=(S/'CurrentCompactCallerModelV1.lean').read_text();a=s.index('          let r3 ← ops.op20 transport.Variant.S2',s.index('def verifier.candidate.tx1'));b=a+re.search(r'(?m)^ {8}\| core.ops.control_flow.ControlFlow.Break residual =>',s[a:]).start()
body='\n'.join(x[8:] for x in s[a:b].rstrip().splitlines())
assert body in (S/'CurrentCompactTx1ReachabilityV1.lean').read_text()
(E/'accepted-targets.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',qualification='Focused cached source compilation only; no actual SDK whole-cone closure or release replay.',targets=accepted),indent=2)+'\n')
print('PASS exact source adaptation, complete tx1 suffix, current accepted receipts, source-only packet:',len(accepted),'targets')
