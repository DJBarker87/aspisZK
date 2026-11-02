"""Timing-only authorization before invoking the unchanged shared barrier."""
from pathlib import Path
import importlib.util,os,sys
s=importlib.util.spec_from_file_location('guard',Path(__file__).with_name('timing-window-guard.py'));g=importlib.util.module_from_spec(s);s.loader.exec_module(g)
assert sys.argv[1].endswith('/native90119/admission-barrier.json')
g.check(require_live=True)
os.environ['QUIET_WINDOW_OWNER']='1'
barrier='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/barrier.py'
os.execv(sys.executable,[sys.executable,barrier,*sys.argv[1:]])
