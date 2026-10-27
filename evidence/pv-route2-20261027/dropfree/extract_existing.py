from pathlib import Path
import sys
D=Path('/home/dombarker/project-offloads/codex-pv-route2-20261027/dropfree');import runpy; args=sys.argv[:];sys.argv=[args[0]];globals().update(runpy.run_path(str(D/'run.py')));sys.argv=args
op=int(sys.argv[1]);prior=sys.argv[2];suffix=sys.argv[3];out=D/f'generated-{op}-{suffix}';out.mkdir()
run(f'aeneas-{op}-{suffix}',['timeout','180','/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools/aeneas','-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace',f'PV_R2_DF_{op}_{suffix}','-dest',str(out),'-split-files','-emit-json',str(D/f'PV_R2_DF_{op}_{prior}.llbc')])
