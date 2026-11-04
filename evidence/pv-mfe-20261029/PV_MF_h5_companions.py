from pathlib import Path
import json
D=Path('/home/dombarker/project-offloads/codex-pv-mfe-20261029');added=[]
for q in (D/'h5-objects').rglob('*.olean'):
 if not q.is_symlink():continue
 p=q.resolve()
 for src in list(p.parent.glob(p.name+'.*'))+[p.with_suffix('.ilean')]:
  if src.exists():
   dst=q.parent/src.name
   if not dst.exists():dst.symlink_to(src);added.append(str(dst.relative_to(D)))
c=dict(failed_attempt=70321,next_attempt=70322,failure_class='before elaboration: missing Init.olean.server companion',source_unchanged=True,correction='Retain verified .olean links and add read-only links to their existing companions in the same original directory',added=added)
(D/'environment-correction-70321.json').write_text(json.dumps(c,indent=2)+'\n');p=D/'lean-70321/result.json';j=json.load(open(p));j.update(original_failure_classification=dict(elaboration_failed=j['elaboration_failed'],environment_failed=j['environment_failed']),elaboration_failed=False,environment_failed=True,classification_correction='environment-correction-70321.json');p.write_text(json.dumps(j,indent=2)+'\n');print('companions',len(added))
