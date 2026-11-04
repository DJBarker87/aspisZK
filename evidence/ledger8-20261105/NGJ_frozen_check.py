from pathlib import Path
import json,lzma,subprocess,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1];F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
L=json.loads(lzma.decompress((E/'NGJ_LEDGER.json.xz').read_bytes()));files={};bad=[]
for r in L['rows']:
 p=r['source_file']
 if p not in files:files[p]=subprocess.check_output(['git','show',F+':'+p],cwd=R)
 raw=files[p];a,b=r['frozen_body_byte_range'];h=hashlib.sha256(raw[a:b]).hexdigest()
 if h!=r['frozen_body_sha256']:bad.append(dict(row=r['row'],function=r['function'],expected=r['frozen_body_sha256'],actual=h))
x=dict(frozen_revision=F,rows=len(L['rows']),source_files=[dict(path=p,sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw)) for p,raw in files.items()],body_mismatches=bad,prover_runs=0)
(E/'NGJ_FROZEN_BODIES.json').write_text(json.dumps(x,indent=1)+'\n');assert not bad,bad
print('All',len(L['rows']),'frozen bodies match')
