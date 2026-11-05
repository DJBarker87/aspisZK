from pathlib import Path
import json,re,subprocess,hashlib
E=Path(__file__).resolve().parent;baseline=E.parent/'pool-retarget-20261105/NGK_EXPECTED_IMPORTS.jsonl'
rows={r['module']:r for r in map(json.loads,baseline.read_text().splitlines())};pins=[]
# Independent committed source inventory, NOT the candidate scan's import lists.
paths=subprocess.check_output(['git','ls-files','evidence/slice-d-prepare-20261104'],text=True).splitlines()
for path in paths:
 p=Path(path)
 if p.suffix!='.lean' or p.parent.as_posix()!='evidence/slice-d-prepare-20261104':continue
 source=subprocess.check_output(['git','show','HEAD:'+path],text=True)
 imports=['Init']+list(dict.fromkeys(re.findall(r'^import ([\w.]+)',source,re.M)))
 if p.stem not in rows:
  rows[p.stem]=dict(module=p.stem,imports=imports)
  pins.append(dict(module=p.stem,path=path,source_sha256=hashlib.sha256(source.encode()).hexdigest(),imports=imports))
for p in E.glob('NGU_*.lean'):
 rows[p.stem]=dict(module=p.stem,imports=['Init']+list(dict.fromkeys(re.findall(r'^import ([\w.]+)',p.read_text(),re.M))))
(E/'NGU_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(rows[n])+'\n' for n in sorted(rows)))
(E/'NGU_BASELINE_PROVENANCE.json').write_text(json.dumps(dict(source=str(baseline),sha256=hashlib.sha256(baseline.read_bytes()).hexdigest(),new_modules='Actual NGU source imports; implicit Init; order-preserving deduplication',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),added_committed_NFW_sources=pins,scan_inputs_used_to_derive_imports=False),indent=1)+'\n')
