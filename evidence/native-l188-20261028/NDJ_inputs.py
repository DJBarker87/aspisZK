"""Pin the explicit evidence inputs; no inferred semantic credit."""
from pathlib import Path
import json,hashlib,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1]
def sha(b):return hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=R)
snapshot=json.loads((E/'NDJ_COVERAGE.json').read_text())['snapshot_revision']
paths=set(json.loads((E/'NDJ_NCZ_SNAPSHOT.json').read_text())['evidence_manifest'])
# Entire cited release packets and merged frontier packets, including receipts,
# patch/source snapshots and controls; contents remain in immutable Git.
prefixes=['evidence/native-elfpins-20261028/','evidence/native-elfscope-20261028/','evidence/native-featparity-20261028/','evidence/kani-undet-20261028/','evidence/native-sbfstack-20261028/','evidence/native-front1-20261028/','evidence/native-front3-20261028/','evidence/native-front4-20261028/','evidence/replay-deployed2-20261027/','evidence/joint-sha453-20261028/','evidence/joint-agg1-20261028/','evidence/joint-agg2-20261028/','evidence/lowering2-20261026/','evidence/l188-audit1-20261027/','evidence/joint-pda-20261028/']
paths.update(p for p in git('ls-tree','-r','--name-only',snapshot).decode().splitlines() if any(p.startswith(pre) for pre in prefixes))
ndk=json.loads((E/'NDJ_NDK_RESULT.json').read_text())
ndkrev=ndk['package_revision']
extra={p for p in git('ls-tree','-r','--name-only',ndkrev).decode().splitlines() if p.startswith('evidence/native-ledger2-20261028/')}
paths.update(json.loads(__import__('lzma').decompress((E/'NDJ_NDK_SNAPSHOT.json.xz').read_bytes()))['evidence_manifest'])
paths.update(extra)
paths.update(['design/PREMISE-LEDGER-20261025.md','design/TRUST-INVENTORY-APPENDIX-DRAFT-20261027.md','lean/JHx_Joint.lean','lean/JHu_FixturePdaRuntime.lean','lean/CPH_Game.lean','lean/F3T_Numeric.lean','lean/F3U_RangeEdges.lean','docs/research/100bit-spend-path-20261013/design/SECURITY-CONTRACT-20261021.md','docs/research/100bit-spend-path-20261013/lean/PerAttemptEnvelope.lean'])
proc=subprocess.Popen(['git','cat-file','--batch'],cwd=R,stdin=subprocess.PIPE,stdout=subprocess.PIPE);pins={}
for path in sorted(paths):
 revision=ndkrev if path in extra else snapshot
 proc.stdin.write((revision+':'+path+'\n').encode());proc.stdin.flush();meta=proc.stdout.readline().split();assert len(meta)==3 and meta[1]==b'blob',path
 size=int(meta[2]);h=hashlib.sha256();left=size
 while left:
  b=proc.stdout.read(min(left,1024*1024));assert b;h.update(b);left-=len(b)
 assert proc.stdout.read(1)==b'\n'
 pins[path]=dict(revision=revision,sha256=h.hexdigest(),bytes=size)
proc.stdin.close();assert proc.wait()==0
local={}
for p in E.rglob('*'):
 if not p.is_file() or '__pycache__' in p.parts:continue
 if p.name in ['NDJ_EVIDENCE_PINS.json','NDJ_VALIDATION.json','NDJ_VALIDATION.log','NDJ_VALIDATION_TIME.log']:continue
 local[str(p.relative_to(R))]=dict(sha256=sha(p.read_bytes()),bytes=p.stat().st_size)
(E/'NDJ_EVIDENCE_PINS.json').write_text(json.dumps(dict(snapshot_revision=snapshot,git=pins,local=local),indent=2,sort_keys=True)+'\n')
print(json.dumps(dict(git_files=len(pins),local_files=len(local))))
