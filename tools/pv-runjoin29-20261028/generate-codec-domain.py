"""The monolithic predicate exceeded elaborator depth; use bounded stages."""
import runpy
from pathlib import Path
runpy.run_path(str(Path(__file__).with_name('generate-staged-codec-domain.py')),run_name='__main__')
