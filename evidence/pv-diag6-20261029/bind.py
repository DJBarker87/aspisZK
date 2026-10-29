from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-diag6-20261029');P=D.parent/'codex-pv-diag3-20261029'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
b=json.loads((P/'binding.json').read_text());rows=[]
for r in b['bindings']:
 if r['source']['name'] not in ['write_all','default_write_fmt','write_fmt','unix_fd_write','unix_stdio','lazy_drop','box_drop','vec_drop','rawvec_drop','anyhow_drop']:continue
 src=r['source'];assert sha(Path(src['path']))==src['file_sha256']
 last=-1
 for needle in r['ordered_checks']:
  k=src['text'].find(needle,last+1);assert k>=0;last=k
 rows.append(r)
(D/'source-bindings.json').write_text(json.dumps(dict(evidence_class='own-1 partial structural association, inherited complete source regions rechecked',inherited_binding_sha256=sha(P/'binding.json'),bindings=rows,new_joint_theorems=['unwind_joint','scope_joint','write_step_joint','write_prefix_joint','formatter_joint','write_fmt_joint','adapter_joint','stderr_joint','ignored_write_joint','report_joint'],meaning='Control composition retains every complete callee execution; native callee contracts and same-original-L1-coin coupling are unproved P obligations.',compiler_boundary='V370 / owner pending D381/D386',features=b['resolved_build_units'],whole_native_joint_law=False),indent=2)+'\n');print('rechecked',len(rows),'source regions; no native leaf independence asserted')
