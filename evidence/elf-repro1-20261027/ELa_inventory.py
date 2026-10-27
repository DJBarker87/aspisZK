import json,hashlib,pathlib,subprocess
P=pathlib.Path('/home/dombarker/project-offloads'); x=json.load(open(P/'codex-cx-elf-repro1-20261027/ELa_historical.json'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r={}
for name in ['codex-cx-lowering2-20261026','codex-cx-sbf-recapture-20261024']:
 s=P/name/'src'; rows=[]
 for f in x['source_checks']:
  p=s/f['path']; actual=sha(p) if p.is_file() else None
  rows.append(dict(path=f['path'],expected=f['expected_sha256'],actual=actual))
 r[name]=dict(checked=len(rows),mismatches=[f for f in rows if f['expected']!=f['actual']])
paths=[pathlib.Path('/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf'),pathlib.Path('/home/dombarker/.cache/solana/v1.52/platform-tools/rust/bin/rustc'),P/'codex-cx-lowering2-20261026/rustc-diagnostics.py']
r['tools']=[dict(path=str(p),sha256=sha(p)) for p in paths]
r['version']=subprocess.check_output([str(paths[0]),'--version'],text=True)
r['historical_workspace_present']=(P/'codex-cx-s10-repin3-20261023').exists()
print(json.dumps(r,indent=2))
