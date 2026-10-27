from pathlib import Path
import shutil, json, hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-extract-20261027')
P=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/rng-extractor')
D.mkdir(exist_ok=True)
for name in ['base','charon','deps']:
 shutil.copytree(P/name,D/'pipeline'/name,symlinks=True,ignore=shutil.ignore_patterns("_build",".git",".github",".claude"))
p=D/'pipeline/base/src/Main.ml'; s=p.read_text(); start=s.index('      (* ProverRwRngExtractor006:'); end=s.index('      (* Apply the pre-passes *)',start)
(D/'removed-preflight.ml').write_text(s[start:end]); p.write_text(s[:start]+s[end:])
shutil.copy2(P/'build-base.sh',D/'pipeline/build-base.sh')
for n in ['charon','charon-driver']:
 shutil.copy2(Path('/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools')/n,D/n)
print(json.dumps({'copy':str(D),'pinned_Main_sha256':hashlib.sha256((P/'base/src/Main.ml').read_bytes()).hexdigest(),'diagnostic_Main_sha256':hashlib.sha256(p.read_bytes()).hexdigest()}))
