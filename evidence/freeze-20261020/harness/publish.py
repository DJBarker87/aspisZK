#!/usr/bin/env python3
"""Collect small text evidence; retain binaries and large logs on the host."""
from pathlib import Path
import hashlib,json,shutil
H=Path('/home/dombarker/project-offloads/codex-cx-pin-20261020');P=H/'publication';P.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Copy complete command/time/resource receipts; hash large trace/debug streams.
for p in (H/'receipts').rglob('*'):
 if not p.is_file():continue
 r=p.relative_to(H);out=P/r;out.parent.mkdir(parents=True,exist_ok=True)
 if p.suffix=='.text' or p.stat().st_size>1024*1024:
  out.with_name(out.name+'.pin.json').write_text(json.dumps(dict(host_path=str(p),sha256=sha(p),bytes=p.stat().st_size),indent=2)+'\n')
 else:shutil.copy2(p,out)
for name in ['cu.json','llbc-comparison.json','source-hashes.json','artifacts-sha256.txt','toolchains.txt','reservations.txt','r1-devnet.template.json','plan.log','validation.json','test-results.json']:
 if (H/name).exists():shutil.copy2(H/name,P/name)
for name in ['charon-input.json','aeneas-input.json']:
 if (H/'extraction-freeze'/name).exists():shutil.copy2(H/'extraction-freeze'/name,P/name)
for p in (H/'stack').glob('*/stack-audit.json'):
 out=P/'stack'/p.parent.name/p.name;out.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,out)
for p in (H/'runs').rglob('evidence.json'):
 if 'adopt' in p.parts:continue
 out=P/p.relative_to(H);out.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,out)
for name in ['r1p-retry-gate.json','simulator.json']:
 if (H/'runs'/name).exists():shutil.copy2(H/'runs'/name,P/name)
rec=[]
for p in sorted((H/'receipts').glob('*/receipt.json')):
 r=json.loads(p.read_text());rec.append(dict(name=p.parent.name,**r))
(P/'runs.json').write_text(json.dumps(rec,indent=2)+'\n')
print(len(rec),'completed command receipts')
