"""Read-only predecessor validation with the sole report destination relocated."""
from pathlib import Path
import json,runpy,hashlib,difflib
E=Path(__file__).resolve().parent;P=E.parent/'slice-d-entry6-20261107'
raw=(P/'NIS_final_check.py').read_text()
s=raw.replace('E=Path(__file__).resolve().parent','E=Path('+repr(str(P))+')').replace("(E/'NIS_AUDIT.json').write_text", "(Path("+repr(str(E))+ ")/'NIU_NIS_REVALIDATION.json').write_text")
(E/'NIU_NIS_validation.diff').write_text(''.join(difflib.unified_diff(raw.splitlines(True),s.splitlines(True))))
exec(compile(s,str(P/'NIS_final_check.py'),'exec'),{'__name__':'NIU_readonly_revalidation','__file__':str(P/'NIS_final_check.py')})
p=E.parent/'verify-observed4-20261107/NIH_validate.py'
r=runpy.run_path(str(p))['validate']()
(E/'NIU_NIH_REVALIDATION.json').write_text(json.dumps(r,indent=1)+'\n')
print(json.dumps(dict(stage='prior-validation',NIS='PASS',NIH=r['status'])))
