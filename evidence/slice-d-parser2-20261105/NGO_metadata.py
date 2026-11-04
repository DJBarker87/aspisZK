"""Reconstruct missing full feature-vector artifact; never invokes Kani."""
from pathlib import Path
import subprocess,json,hashlib,sys
B=Path(__file__).resolve().parent;x=json.loads((B/sys.argv[1]).read_text());a=x['attempt'];S=B/'NGO_src'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
frozen='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
assert sha(S/'Cargo.lock')==frozen
r=subprocess.run(['/home/dombarker/.cargo/bin/cargo','metadata','--locked','--offline','--format-version','1','--features','aspis-r1-cost-probe/optimized-terminal,aspis-r1-cost-probe/program-build'],cwd=S,capture_output=True,text=True)
assert r.returncode==0,r.stderr
full=next(l for l in r.stdout.splitlines()if l.startswith('{'))+'\n'
assert hashlib.sha256(r.stdout.encode()).hexdigest()=='04ef9d4f78905271c5ae740dcaf75d1f72b8b6b68f8305b87aea25004efb62d1'
(B/(a+'-graph-full.json')).write_text(full)
m=json.loads(full);p={p['id']:p for p in m['packages']}
features=[dict(name=p[n['id']]['name'],version=p[n['id']]['version'],source=p[n['id']].get('source'),features=n['features'])for n in m['resolve']['nodes']]
(B/(a+'-graph-features.json')).write_text(json.dumps(features,indent=1))
assert sha(S/'Cargo.lock')==frozen
(B/(a+'-graph-reconstruction.json')).write_text(json.dumps(dict(claim='Evidence artifact only; no Kani or native proof rerun',raw_stdout_sha256=hashlib.sha256(r.stdout.encode()).hexdigest(),all_resolved_crates=len(features),lock_unchanged=True,lock_sha256=frozen,historical_binding='Exact same pre-run graph hash in K003 through K017; features for all resolved crates, including unreached workspace members'),indent=1))
print(json.dumps(dict(metadata_only=True,all_resolved_crates=len(features),graph_sha256=hashlib.sha256(r.stdout.encode()).hexdigest(),lock_unchanged=True)))
