"""Recover one missing raw metadata artifact, requiring byte-for-byte hash identity."""
from pathlib import Path
import subprocess,json,hashlib,lzma
B=Path(__file__).resolve().parent;S=B/'NGN_src';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();before=sha(S/'Cargo.lock')
r=subprocess.run(['/home/dombarker/.cargo/bin/cargo','metadata','--locked','--offline','--format-version','1','--features','aspis-r1-cost-probe/optimized-terminal,aspis-r1-cost-probe/program-build'],cwd=S,text=True,capture_output=True);assert r.returncode==0,r.stderr
raw=r.stdout.encode();h=hashlib.sha256(raw).hexdigest();assert [h]==json.loads((B/'NGN_EXPECTED_GRAPH_HASHES.json').read_text()),'STOP metadata does not reproduce every native receipt'
assert sha(S/'Cargo.lock')==before=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
x=json.loads(r.stdout);nodes={n['id']:n for n in x['resolve']['nodes']};out=[dict(name=p['name'],version=p['version'],source=p.get('source'),features=nodes[p['id']]['features']) for p in x['packages']]
(B/'NGN_FULL_GRAPH.json.xz').write_bytes(lzma.compress(raw));(B/'NGN_FULL_GRAPH.json.sha256').write_text(h+'\n');(B/'NGN_ALL_CRATE_FEATURES.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(dict(graph_sha256=h,all_crates=len(out),lock_unchanged=True,interpretation='same complete raw cargo metadata artifact matches the SHA256 in every earlier native graph receipt; no Kani replay')))
