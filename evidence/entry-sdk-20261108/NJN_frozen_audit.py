from pathlib import Path
import json,lzma,subprocess,hashlib
E=Path(__file__).resolve().parent;idx=json.loads((E/'NJN_INPUTS.json').read_text());h=idx['attempts']['NJN_K001']['NGL_FROZEN_SOURCE_PINS.json'];pins=json.loads(lzma.decompress((E/idx['objects'][h]['path']).read_bytes()))
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';rows=[]
for n,h in pins.items():
 p=subprocess.run(['git','show',rev+':'+n],capture_output=True)
 actual=hashlib.sha256(p.stdout).hexdigest() if p.returncode==0 else None
 rows.append(dict(path=n,expected=h,actual=actual,match=actual==h))
lock=subprocess.check_output(['git','show',rev+':Cargo.lock']);kh=idx['attempts']['NJN_K001']['NIJ_src/Cargo.lock'];actual_lock=lzma.decompress((E/idx['objects'][kh]['path']).read_bytes());assert lock==actual_lock
x=dict(revision=rev,files=len(rows),mismatches=[r for r in rows if not r['match']],source_manifest_sha256=hashlib.sha256(json.dumps(pins,sort_keys=True).encode()).hexdigest(),lock_sha256=hashlib.sha256(lock).hexdigest(),lock_identical=True)
(E/'NJN_FROZEN_CHECK.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps(dict(files=len(rows),mismatches=len(x['mismatches']),lock_identical=True)))
