#!/usr/bin/env python3
"""Audit final focused receipts and the unchanged starting source scope."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/port4b-20261023'
L=R/'docs/research/100bit-spend-path-20261013/lean'
start='986dc0bd7daf04ecd14cd0459585855277fef937'
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('lean-*/receipt.json'))]
assert len(receipts)<=100
final={}
for src in sorted(L.glob('Port4B_*.lean')):
 data=src.read_bytes();sha=hashlib.sha256(data).hexdigest()
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats)',src.read_text()),src
 hits=[r for r in receipts if r['exit_status']==0 and r['source_hashes'].get(src.name)==sha]
 assert hits,src
 hit=hits[-1]
 assert hit['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 for line in hit['print_axioms']:
  if 'depends on axioms:' in line:
   names=line.split('[',1)[1].split(']',1)[0].split(', ')
   assert set(names)<={'propext','Classical.choice','Quot.sound'},line
 final[src.name]={'sha256':sha,'receipt':hit['attempt'],'axioms':hit['print_axioms']}
changed=subprocess.check_output(['git','diff','--name-only',start],cwd=R,text=True).splitlines()
allowed=lambda p:p.startswith(('evidence/port4b-20261023/','tools/port4b-20261023/')) or p.startswith(str(L.relative_to(R))+'/Port4B_')
assert all(allowed(p) for p in changed),changed
out={'schema':'focused-extractor-proof-packet-v1','start_revision':start,
 'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
 'actual_lean_attempts':len(receipts),'kani_runs':0,'final_modules':final,
 'changed_paths':changed,'shipped_source_changed':False,'elf_rebuild_triggered':False,
 'limits':'6G high/8G max/no swap/64 tasks; never raised',
 'scope':'Focused module union only. Scoped accepted batch/TX1/TX2 transport is proved under named P6 local lowerings and explicit S1 PreparedBinding/parser-model provenance. Concrete upstream binding instances remain open; target not yet established. No total error-preserving transport, release replay or security conclusion.'}
(E/'manifest.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'modules':len(final),'lean':len(receipts),'kani':0,'shipped_source_changed':False}))
