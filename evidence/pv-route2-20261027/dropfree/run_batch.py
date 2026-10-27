from pathlib import Path
import sys,runpy
D=Path('/home/dombarker/project-offloads/codex-pv-route2-20261027/dropfree');sys.argv=[sys.argv[0]];globals().update(runpy.run_path(str(D/'run.py')))
run('scope-missing-01',['python3',str(D/'batch_phases.py'),str(D/'batch-missing-01')],D)
