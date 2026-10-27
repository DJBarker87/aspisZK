"""Run the frozen analyzer once, after marker removal, inside admitted caps."""
import pathlib, subprocess, time, json, hashlib, sys
b=pathlib.Path('/home/dombarker/project-offloads/codex-pv-dudect-20261027');r=b/'d294';o=b/'window-1793111961'
assert not (b.parent/'QUIET_WINDOW.json').exists()
assert json.loads((r/'analysis-admission.json').read_text())['allowed'] is True
cg=pathlib.Path('/sys/fs/cgroup'+pathlib.Path('/proc/self/cgroup').read_text().split('0::')[1].strip())
limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert list(limits.values())==['6442450944','8589934592','0','64']
cmd=['/usr/bin/time','-v','-o',str(r/'analysis-time.log'),'python3',str(b/'src/tools/pv-dudect/analyze.py'),str(o)]
start=time.time()
with (r/'analysis.json').open('x') as out,(r/'analysis.stderr').open('x') as err:
    run=subprocess.run(cmd,stdout=out,stderr=err)
rec=dict(target=cmd,exit_status=run.returncode,start_epoch=start,end_epoch=time.time(),wall_seconds=time.time()-start,peak_rss_scope_bytes=int((cg/'memory.peak').read_text()),swap_peak_bytes=int((cg/'memory.swap.peak').read_text()),limits=limits,source_revision='cc5fdf3956',candidate_revision='73070ddd512bc4e79edfc0db714fb64dc74e87b8',print_axioms='N/A: no Lean',analyzer_sha256=hashlib.sha256((b/'src/tools/pv-dudect/analyze.py').read_bytes()).hexdigest())
(r/'analysis-receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
sys.exit(run.returncode)
