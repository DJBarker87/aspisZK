"""Scan current emission and associate finite write evidence conservatively."""
from pathlib import Path
s=Path('tools/pv-b3p6-20261028/fidelity227_resume5.py').read_text().replace("raw227-complete-resume5/Funs.lean","raw227-composition-resume5/Funs.lean").replace('len(rows)==191','len(rows)==197').replace('definitions=191','definitions=197').replace("fidelity227-resume5.json","fidelity227-current-scan-resume5.json")
exec(compile(s,'current-fidelity-scan','exec'))
