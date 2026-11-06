from pathlib import Path
import json,lzma,hashlib,shutil
B=Path.cwd();x=json.loads(lzma.decompress((B/'NLC_CLOSURE_PINS.json.xz').read_bytes()));bad=[]
for r in x['selected_objects']:
 p=Path(r['path'])
 if not p.exists() or hashlib.sha256(p.read_bytes()).hexdigest()!=r['sha256']:bad.append(str(p))
assert not bad,bad
out=dict(selected_objects=len(x['selected_objects']),unchanged=True,mismatches=bad,disk=shutil.disk_usage(B)._asdict(),source_to_elf_rebuild=False,keys_or_wallets_touched=False)
(B/'NLC_FINAL_PINS.json').write_text(json.dumps(out,indent=2));print('Final selected objects unchanged since combined pin/export; no prover replay')
