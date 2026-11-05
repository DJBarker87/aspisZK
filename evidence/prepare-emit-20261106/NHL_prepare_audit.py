"""Own audit inputs: unchanged walker; module/root lists and source imports."""
from pathlib import Path
import json,hashlib,subprocess,difflib,re
E=Path(__file__).resolve().parent;R=E.parent.parent
P=R/'evidence/candidate-prepare-20261106'
for n in ['Driver','ProofDriver']:
 s=(P/f'NHF_{n}.lean').read_text().replace('NHF_','NHL_')
 (E/f'NHL_{n}.lean').write_text(s)
(E/'NHL_batch.py').write_text((P/'NHF_batch.py').read_text().replace('NHF_','NHL_'))
(E/'NHL_native').mkdir(exist_ok=True)
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 (E/'NHL_native'/n).write_bytes((P/'NHF_native'/n).read_bytes())
walker=R/'evidence/axaudit2-20261102/NEP_WALKER.lean'
(E/'NHL_WALKER_SOURCE.lean.txt').write_bytes(walker.read_bytes())
(E/'NHL_DRIVER_DIFF.txt').write_text(''.join(difflib.unified_diff((P/'NHF_ProofDriver.lean').read_text().splitlines(True),(E/'NHL_ProofDriver.lean').read_text().splitlines(True),fromfile='admitted NHF driver',tofile='NHL driver')))
# Imported module baselines are evidence, not inferred from a successful run.
base={};conflicts=[]
for path in [P/'NHF_EXPECTED_IMPORTS.jsonl',R/'evidence/transcript-scalars-20261105/NGT_EXPECTED_IMPORTS.jsonl',R/'evidence/prepared-claim2-20261105/NGY_EXPECTED_IMPORTS.jsonl']:
 for line in path.read_text().splitlines():
  row=json.loads(line);name=row['module'];imports=row['imports']
  if name in base and base[name]!=imports:conflicts.append(dict(module=name,first=base[name],next=imports,source=str(path)))
  else:base[name]=imports
ngq_path='evidence/transcript-queries-20261105/NGQ_EXPECTED_IMPORTS.jsonl'
ngq_raw=subprocess.check_output(['git','show','HEAD:'+ngq_path])
for line in ngq_raw.decode().splitlines():
 row=json.loads(line);name=row['module'];imports=row['imports']
 if name in base and base[name]!=imports:conflicts.append(dict(module=name,first=base[name],next=imports,source=ngq_path))
 else:base[name]=imports
for path in E.glob('NHL_*.lean'):
 base[path.stem]=['Init']+re.findall(r'^import ([\w.]+)',path.read_text(),re.M)
(E/'NHL_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps({'module':n,'imports':xs})+'\n' for n,xs in sorted(base.items())))
(E/'NHL_BASELINE_INPUTS.json').write_text(json.dumps({'conflicts':conflicts,'walker_sha256':hashlib.sha256(walker.read_bytes()).hexdigest(),'sources':[{'path':str(p.relative_to(R)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in [P/'NHF_EXPECTED_IMPORTS.jsonl',R/'evidence/transcript-scalars-20261105/NGT_EXPECTED_IMPORTS.jsonl',R/'evidence/prepared-claim2-20261105/NGY_EXPECTED_IMPORTS.jsonl']]},indent=1)+'\n')
assert not conflicts,conflicts[:3]
print(len(base),'baselines prepared')
