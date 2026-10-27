from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-leaf-p6-14-20261027'
for p in E.glob('LPp_*.rs'):
 crate='aspis-core' if p.stem=='LPp_usize_capture' else 'aspis-r1-cost-probe'
 subprocess.run(['scp','-q',str(p),H+':'+B+'/LPp_src/crates/'+crate+'/src/'+p.name],check=True)
code=f'''from pathlib import Path
import difflib
B=Path('{B}');src=B/'LPp_src';base=Path('/home/dombarker/project-offloads/codex-cx-leaf-p6-13-20261027/LPo_src')
p=src/'crates/aspis-r1-cost-probe/src/sampler.rs'
s=p.read_text().replace('#[cfg(kani)] mod LPp_capture;', '#[cfg(kani)] mod LPp_capture {{ include!("LPp_capture.rs"); }}')
p.write_text(s)
q=src/'crates/aspis-core/src/transcript.rs'
if (src/'crates/aspis-core/src/LPp_usize_capture.rs').exists() and 'mod LPp_usize_capture' not in q.read_text():q.write_text(q.read_text()+'\\n#[cfg(kani)] mod LPp_usize_capture {{ include!("LPp_usize_capture.rs"); }}\\n')
patch=''
for rel in ['crates/aspis-r1-cost-probe/src/sampler.rs','crates/aspis-r1-cost-probe/src/LPp_capture.rs','crates/aspis-core/src/transcript.rs','crates/aspis-core/src/LPp_usize_capture.rs']:
 if not (src/rel).exists():continue
 old=(base/rel).read_text() if (base/rel).exists() else ''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),(src/rel).read_text().splitlines(True),fromfile='a/'+rel if old else '/dev/null',tofile='b/'+rel))
(B/'LPp_harness.patch').write_text(patch)
'''
subprocess.run(['ssh',H,"python3 - <<'PY'\n"+code+'\nPY'],check=True)
subprocess.run(['scp','-q',H+':'+B+'/LPp_harness.patch',str(E/'LPp_harness.patch')],check=True)
