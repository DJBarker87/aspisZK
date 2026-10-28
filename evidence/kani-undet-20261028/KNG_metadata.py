"""Isolated feature resolution; immutable frozen compilation workspace lock."""
from pathlib import Path
import subprocess,json,hashlib,tomllib,sys
b=Path(__file__).resolve().parent;s=b/'KNG_src';h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
frozen='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef';assert h(s/'Cargo.lock')==frozen
crate=sys.argv[2];d=b/('KNG_meta_'+crate);d.mkdir(exist_ok=True)
# The secondary metadata-only wrapper is never a compiled verifier source.
# Its seed is frozen; generated root edge and unreachable-package pruning are audited.
features=['default','private-leaf-salts','optimized-terminal','program-build'] if crate=='aspis-r1-cost-probe' else ['r0','pool-v1-kernel']+[k for k in tomllib.loads((s/'crates/aspis-statement/Cargo.toml').read_text())['features'] if k in ['pool-v1-pair-forest-packed-digest-audit','pool-v1-pair-forest-packed-digest-selector-tensor-audit','pool-v1-pair-forest-binary-copy-weights-audit','pool-v1-pair-forest-endpoint-selector-cache-audit','pool-v1-pair-forest-semantic-factor-audit','pool-v1-pair-forest-pattern-window-audit','pool-v1-pair-forest-copy-pattern-basis-audit','pool-v1-pair-forest-packed-range-audit','pool-v1-pair-forest-active-mask-basis-audit','pool-v1-pair-forest-copy-selector-tensor-basis-audit','pool-v1-pair-forest-copy-tag-dot-basis-audit','pool-v1-pair-forest-copy-finish-dot-basis-audit']]
manifest='[package]\nname="kng-metadata-root"\nversion="0.0.0"\nedition="2021"\n[workspace]\n[lib]\npath="empty.rs"\n[dependencies]\ntarget={package='+json.dumps(crate)+',path='+json.dumps(str(s/'crates'/crate))+',features='+json.dumps(features)+'}\n'
# Root dev dependencies represented explicitly for resolution (Kani --lib).
if crate=='aspis-statement':manifest+='p3-field="=0.6.1"\np3-mersenne-31="=0.6.1"\np3-symmetric="=0.6.1"\nsha2="0.10.8"\n'
(d/'Cargo.toml').write_text(manifest);(d/'empty.rs').write_text('')
if not (d/'Cargo.lock').exists():(d/'Cargo.lock').write_bytes((s/'Cargo.lock').read_bytes())
cmd=['/home/dombarker/.cargo/bin/cargo','metadata','--offline','--format-version','1','--manifest-path',str(d/'Cargo.toml')]
r=subprocess.run(cmd,capture_output=True,text=True);assert r.returncode==0,r.stderr
m=json.loads(r.stdout);pk={p['id']:p for p in m['packages']};allowed={(p['name'],p['version'],p.get('source')) for p in tomllib.loads((s/'Cargo.lock').read_text())['package']}
assert all(p['name']=='kng-metadata-root' or (p['name'],p['version'],p.get('source')) in allowed for p in pk.values())
# Reject altered dependency edges between frozen packages, including registry checksums.
fl={(p['name'],p['version'],p.get('source')):p for p in tomllib.loads((s/'Cargo.lock').read_text())['package']}
for p in tomllib.loads((d/'Cargo.lock').read_text())['package']:
 if p['name']=='kng-metadata-root':continue
 q=fl[(p['name'],p['version'],p.get('source'))];assert p.get('checksum')==q.get('checksum')
for n in m['resolve']['nodes']:
 p=pk[n['id']]
 if p['name']=='kng-metadata-root':continue
 deps=fl[(p['name'],p['version'],p.get('source'))].get('dependencies',[])
 for target in n['dependencies']:
  t=pk[target]
  assert any(v.split()[0]==t['name'] and (len(v.split())==1 or v.split()[1]==t['version']) for v in deps),(p['name'],t['name'],deps)
resolved=[dict(id=n['id'],name=pk[n['id']]['name'],version=pk[n['id']]['version'],source=pk[n['id']].get('source'),features=n['features'],deps=n['deps']) for n in m['resolve']['nodes']]
st=next(n for n in resolved if n['name']=='aspis-statement');assert len(st['features'])==14,st
if crate=='aspis-r1-cost-probe':assert set(next(n for n in resolved if n['name']==crate)['features'])==set(features)
assert h(s/'Cargo.lock')==frozen
out=dict(command=cmd,manifest=manifest,compile_features=features,frozen_lock_sha256=frozen,lock_before=frozen,lock_after=h(s/'Cargo.lock'),metadata_wrapper_lock_sha256=h(d/'Cargo.lock'),metadata_wrapper_lock_changes=r.stderr,graph_validated_against_frozen_lock=True,all_resolved_edges_and_checksums_match_frozen=True,resolved_features_per_crate=resolved)
(b/(sys.argv[1]+'-metadata.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
