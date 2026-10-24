"""Pin candidate005 against original accepted base and its immutable build inputs."""
from pathlib import Path
import json,hashlib,difflib,sys
a=int(sys.argv[1]);assert 6<=a<=8
D=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/rng-extractor')
T=Path('/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/aeneas-full')
O=D/f'continuation{a:03d}';O.mkdir()
prov=json.loads((D/'base-provenance.json').read_text());receipt=json.loads((D/f'prover-rw-rng-extractor-build-{a:03d}/receipt.json').read_text());lines=[];manifest={}
for rel,expected in prov['source_manifest'].items():
 if 'sha256' not in expected:continue
 orig=T/rel;p=D/'base'/rel
 assert hashlib.sha256(orig.read_bytes()).hexdigest()==expected['sha256']
 sha=hashlib.sha256(p.read_bytes()).hexdigest();assert receipt['candidate_source_sha256'][rel]==sha
 manifest[rel]=dict(sha256=sha,bytes=p.stat().st_size)
 if sha!=expected['sha256']:
  lines.extend(difflib.unified_diff(orig.read_text().splitlines(True),p.read_text().splitlines(True),fromfile='a/'+rel,tofile='b/'+rel))
(O/f'candidate-{a:03d}.patch').write_text(''.join(lines))
(O/f'candidate-{a:03d}-source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
(O/'build-base005.sh').write_bytes((D/'build-base.sh').read_bytes())
b=D/f'candidate-{a:03d}/main.exe'
if receipt['exit_status']==0:assert hashlib.sha256(b.read_bytes()).hexdigest()==receipt['versioned_binary']['sha256']
(O/f'candidate-{a:03d}-pins.json').write_text(json.dumps(dict(binary=receipt.get('versioned_binary'),build_recipe_sha256=hashlib.sha256((D/'build-base.sh').read_bytes()).hexdigest(),patch_sha256=hashlib.sha256((O/f'candidate-{a:03d}.patch').read_bytes()).hexdigest(),old_binary003_sha256=hashlib.sha256((D/'candidate-003/main.exe').read_bytes()).hexdigest(),status=f'Unadopted candidate{a:03d}; exit {receipt["exit_status"]}; no independent deterministic rebuild',compiler_image='sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7',source_assessment='build source_revision labels reviewed base plus uncommitted job patch; exact source hashes above, not a new shipped identity gate'),indent=2)+'\n')
print('Archived complete candidate005 source association')
