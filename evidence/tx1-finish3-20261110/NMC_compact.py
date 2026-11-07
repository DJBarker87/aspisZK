"""Deduplicate pinned inputs after all scopes stop; preserve exact bytes by hash.

Only own local evidence changes. A *.ref.json resolves to the retained file or
the compressed blob; receipts and source_hashes continue to describe the
uncompressed bytes. This script runs no native, Lean, audit or host command.
"""
from pathlib import Path
from collections import defaultdict
import json,hashlib,lzma
E=Path(__file__).resolve().parent
assert (E/'NMC_L140/receipt.json').exists(),'Wait for the last scope and retrieval'
assert not (E/'NMC_CLIENT_ACTIVE').exists(),'No active client'
H=lambda b:hashlib.sha256(b).hexdigest()
pool=defaultdict(list)
for p in E.rglob('*'):
 if p.is_file()and p.stat().st_size>=100_000 and 'NMC_inputs'not in p.parts:
  pool[H(p.read_bytes())].append(p)
records=[];saved=0
for sha,paths in pool.items():
 selected=[p for p in paths if '/sources/'in str(p)or(p.parent==E and p.name.endswith('-graph.json'))]
 if not selected:continue
 retained=[p for p in paths if p not in selected]
 if not retained and len(selected)<2:continue
 blob=selected[0].read_bytes();assert H(blob)==sha
 if retained:
  target=min(retained,key=lambda p:(len(p.parts),str(p)))
  encoding='identity'
 else:
  target=E/'NMC_inputs'/(sha+'.xz');target.parent.mkdir(exist_ok=True)
  target.write_bytes(lzma.compress(blob));target.with_suffix('.sha256').write_text(sha+'\n')
  encoding='xz'
 for p in selected:
  assert H(p.read_bytes())==sha
  ref=dict(path=str(p.relative_to(E)),retained=str(target.relative_to(E)),encoding=encoding,sha256=sha,bytes=len(blob))
  p.with_name(p.name+'.ref.json').write_text(json.dumps(ref,indent=1)+'\n');p.unlink();records.append(ref);saved+=len(blob)
 # Independently decode the retained payload, rather than trusting compression.
 assert H(lzma.decompress(target.read_bytes())if encoding=='xz'else target.read_bytes())==sha
out=dict(status='PASS_EXACT_BYTE_RETENTION',references=records,removed_duplicate_bytes=saved,no_scope_or_proof_rerun=True)
(E/'NMC_INPUT_REFERENCES.json').write_text(json.dumps(out,indent=1)+'\n')
if (E/'NMC_AUDIT.json').exists():
 audit=json.loads((E/'NMC_AUDIT.json').read_text())
 audit['input_storage']=dict(index='NMC_INPUT_REFERENCES.json',exact_byte_retention=True,references=len(records),removed_duplicate_bytes=saved,graph_references=sum(r['path'].endswith('-graph.json')for r in records),unique_graph_sha256=sorted({r['sha256']for r in records if r['path'].endswith('-graph.json')}))
 (E/'NMC_AUDIT.json').write_text(json.dumps(audit,indent=2)+'\n')
print(json.dumps(dict(status=out['status'],references=len(records),removed_duplicate_bytes=saved)))
