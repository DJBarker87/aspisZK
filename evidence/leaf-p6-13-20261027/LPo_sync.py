from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-leaf-p6-13-20261027'
subprocess.run(['scp','-q',str(E/'LPo_candidate.rs'),H+':'+B+'/LPo_src/crates/aspis-r1-cost-probe/src/LPo_candidate.rs'],check=True)
code=f'''from pathlib import Path
import difflib
B=Path('{B}');s=B/'LPo_src';base=Path('/home/dombarker/project-offloads/codex-cx-leaf-p6-12-20261027/LPn_src')
out=''
for rel in ['crates/aspis-r1-cost-probe/src/candidate.rs','crates/aspis-r1-cost-probe/src/LPo_candidate.rs']:
 old=(base/rel).read_text() if (base/rel).exists() else ''
 out+=''.join(difflib.unified_diff(old.splitlines(True),(s/rel).read_text().splitlines(True),fromfile='a/'+rel if old else '/dev/null',tofile='b/'+rel))
(B/'LPo_harness.patch').write_text(out)
'''
subprocess.run(['ssh',H,"python3 - <<'REMOTE'\n"+code+'\nREMOTE'],check=True)
subprocess.run(['scp','-q',H+':'+B+'/LPo_harness.patch',str(E/'LPo_harness.patch')],check=True)
