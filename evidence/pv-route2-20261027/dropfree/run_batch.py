from pathlib import Path
import sys,runpy
D=Path('/home/dombarker/project-offloads/codex-pv-route2-20261027/dropfree');suffix=sys.argv[1] if len(sys.argv)>1 else '01';sys.argv=[sys.argv[0]];globals().update(runpy.run_path(str(D/'run.py')))
run('scope-missing-'+suffix,['python3',str(D/'batch_phases.py'),str(D/('batch-missing-'+suffix))],D)
