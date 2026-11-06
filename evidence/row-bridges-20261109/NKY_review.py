from pathlib import Path
import json,hashlib,lzma,subprocess,re
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
# Every immutable predecessor native input, checked once by content hash.
p=E.parent/'tx2-adapters2-20261108';idx=json.loads((p/'NKP_INPUTS.json').read_text());seen={};attempts=[]
for n in range(2,46):
 a=f'NKP_K{n:03}'
 for name,h in idx['attempts'][a].items():
  if h not in seen:
   z=p/idx['objects'][h]['path'];b=lzma.decompress(z.read_bytes());assert sha(b)==h
   seen[h]=dict(archive=str(z.relative_to(E.parent.parent)),sha256=h,bytes=len(b))
 r=json.loads((p/a/'receipt.json').read_text());graph=json.loads((p/(a+'-graph-check.json')).read_text());lock=json.loads((p/(a+'-lock-check.json')).read_text());assert graph['graph_matches_frozen']and lock['unchanged']
 attempts.append(dict(attempt=a,exit=r['exit_status'],receipt=str((p/a/'receipt.json').relative_to(E.parent.parent)),receipt_sha256=sha((p/a/'receipt.json').read_bytes())))
(E/'NKY_NKP_REUSE.json').write_text(json.dumps(dict(status='REVALIDATED_IMMUTABLE_INPUTS_AND_GATE_RECEIPTS_NOT_RERUN',attempts=attempts,inputs=list(seen.values())),indent=1)+'\n')
# Frozen source check is read-only; no ELF rebuild is triggered by evidence work.
freeze='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
r=subprocess.run(['git','diff','--quiet',freeze,'--','crates','programs/r1-cost-probe','Cargo.lock'])
pool=subprocess.check_output(['git','rev-parse','b936275465'],text=True).strip()
(E/'NKY_FROZEN.json').write_text(json.dumps(dict(frozen_revision=freeze,source_identity_exit=r.returncode,pool_revision=pool,shipped_source_changed=False,elf_rebuild_trigger=False,elf_pins_inherited_not_reproduced=dict(default='f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4',devnet='63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299',pool='e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc')),indent=1)+'\n');assert r.returncode==0
# Register exact cut assertions and source-file content hashes.
inputs=json.loads((E/'NKY_INPUTS.json').read_text());certs=[]
for a in ['NKY_K008','NKY_K011','NKY_K015','NKY_K018']:
 names=inputs['attempts'][a];name=next(n for n in names if n.endswith('_ownership.rs')or n.endswith('_frame.rs'));h=names[name];raw=lzma.decompress((E/inputs['objects'][h]['path']).read_bytes()).decode()
 assertions=re.findall(r'assert!\([^;]+;',raw)
 certs.append(dict(attempt=a,source=name,sha256=h,assertions=assertions,classification='ReviewedTranscription; P6/D188 option A reclassification, no trust addition/removal'))
(E/'NKY_CERTIFICATES.json').write_text(json.dumps(certs,indent=1)+'\n')
print('inherited native inputs, frozen source and exact cut assertions checked')
