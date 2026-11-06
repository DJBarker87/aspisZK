"""Fail-closed finalizer; a partial gate must never promote candidates."""
from pathlib import Path
import runpy
runpy.run_path(str(Path(__file__).with_name('NKH_stop_finalize.py')),run_name='__main__')
