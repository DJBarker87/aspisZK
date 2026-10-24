"""Export small evidence only; oversized generated JSON retained remotely by hash/size."""
from pathlib import Path
import json,hashlib,shutil
D=Path(__file__).resolve().parent;P=D/'packet';E=D/'export';E.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
large=[]
for p in P.rglob('*'):
 if not p.is_file():continue
 r=p.relative_to(P);q=E/r;q.parent.mkdir(parents=True,exist_ok=True)
 if p.suffix=='.json' and p.stat().st_size>5_000_000:
  large.append(dict(path=str(p),size=p.stat().st_size,sha256=sha(p)))
 else:shutil.copy2(p,q)
pre=json.loads((P/'rust001/preflight.json').read_text());go=json.loads((P/'rust001/go-hashes.json').read_text());post=json.loads((P/'rust001/postrun.json').read_text());receipt=json.loads((P/'rust001/receipt.json').read_text())
pins=pre.pop('source_sha256');receipt.pop('source_sha256')
assert pins==go['source_sha256']==post['source_sha256'] and post['unchanged']
# Retain exact own-stage and dependency source hashes, excluding large sysroot inventory.
relevant={p:v for p,v in pins.items() if not p.startswith('/home/dombarker/.kani/')}
small=dict(schema='ProverRwResumeMIR-pins-v1',preflight=pre,receipt=receipt,all_pre_go_post_equal=True,pin_count=len(pins),source_and_dependencies=relevant,oversized_json=large,full_axioms='N/A: no Lean declarations',elf_pins=dict(default='f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4',devnet='63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299',Pool='121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'),elf_assessment='manager pins retained; no ELF rebuilt or new identity gate')
q=E/'pin-summary.json';q.write_text(json.dumps(small,indent=2)+'\n');assert q.stat().st_size<=5_000_000
print(json.dumps(dict(full_pins=len(pins),relevant_pins=len(relevant),oversized=len(large))))
