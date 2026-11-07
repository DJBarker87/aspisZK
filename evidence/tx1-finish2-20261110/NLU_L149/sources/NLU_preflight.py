from pathlib import Path
import json,hashlib,shutil,lzma
B=Path(__file__).resolve().parent;H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();errors=[]
for n,h in json.loads((B/'NLU_SOURCE_PINS.json').read_text()).items():
 if not (B/'NLU_src'/n).is_file() or H(B/'NLU_src'/n)!=h:errors.append(n)
assert not errors,errors
seed=json.loads((B/'NLU_SEED_PINS.json').read_text());wrong=[]
for r in seed['files']:
 if H(Path(r['destination']))!=r['sha256']:wrong.append(r['destination'])
assert not wrong,wrong
lock=H(B/'NLU_src/Cargo.lock');assert lock=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
usage=shutil.disk_usage(B);own=sum(p.stat().st_size for p in B.rglob('*') if p.is_file());assert own<30000000000
out=dict(status='PASS',source_files=len(json.loads((B/'NLU_SOURCE_PINS.json').read_text())),seed_files=len(seed['files']),seed_bytes=seed['bytes'],lock_sha256=lock,own_bytes=own,disk=usage._asdict(),CARGO_TARGET_DIR=str(B/'NLU_target'),target_not_yet_established=True,new_closed_rows=0)
(B/'NLU_PREFLIGHT.json').write_text(json.dumps(out,indent=1));print(json.dumps(out))
