"""Timing-only authorization before invoking the unchanged shared barrier."""
from pathlib import Path
import importlib.util,os,sys,re
s=importlib.util.spec_from_file_location('guard',Path(__file__).with_name('timing-window-guard.py'));g=importlib.util.module_from_spec(s);s.loader.exec_module(g)
assert re.fullmatch(r'/home/dombarker/project-offloads/codex-pv-uc-20261029/native9112[0-5]/admission-barrier.json',sys.argv[1])
g.check(require_live=True)
os.environ['QUIET_WINDOW_OWNER']='1'
barrier='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/barrier.py'
os.execv(sys.executable,[sys.executable,barrier,*sys.argv[1:]])
