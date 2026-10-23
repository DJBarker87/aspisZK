#!/usr/bin/env python3
"""Pin an accepted translation and enumerate every unbound external template."""
from pathlib import Path
import hashlib,json,re,sys
root=Path(sys.argv[1]);receipt=json.loads(Path(sys.argv[2]).read_text());out=Path(sys.argv[3])
assert receipt['exit_status']==0
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
artifacts={p.name:dict(sha256=sha(p),bytes=p.stat().st_size) for p in sorted(root.iterdir()) if p.is_file()}
external=[]
for name in ['TypesExternal_Template.lean','FunsExternal_Template.lean']:
 p=root/name
 if not p.exists():continue
 text=p.read_text()
 for match in re.finditer(r'^axiom\s+([^\s{(:]+)',text,re.M):
  line=text.count('\n',0,match.start())+1
  external.append(dict(template=name,line=line,name=match.group(1),status='Unbound template hole; not an installed axiom or checked contract'))
inputs=receipt['input_artifacts'];assert inputs and all(v['source_map_consistent_with_live_tree'] for v in inputs.values())
result=dict(translation_attempt=receipt['attempt'],source_revision=receipt['source_revision'],translation_exit_status=0,wall_seconds=receipt['wall_seconds'],peak_rss_kib=receipt['peak_rss_kib'],swaps=receipt['swaps'],inputs=inputs,artifacts=artifacts,external_holes=external,external_hole_count=len(external),lean_compiled=False,source_model_equality_proved=False,whole_run_join_proved=False,print_axioms='N/A: translation only; external templates remain unbound and are not imported into a proof build')
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['translation_attempt','external_hole_count','lean_compiled','source_model_equality_proved']}))
