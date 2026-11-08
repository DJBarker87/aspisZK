"""Run inherited raw ax2 binary by reference, with private job manifests."""
from pathlib import Path
import os,json,hashlib
b=Path(__file__).resolve().parent
p=Path('/home/dombarker/project-offloads/codex-cx-integrate-20261111/NNH_native/NNH_ProofDriver')
assert hashlib.sha256(p.read_bytes()).hexdigest()=='46ee271b392729449147b978830b474e3fa4ecba2b45e03ad13c02490ba6ca3c'
w=b/'NNW_audit_inputs';w.mkdir(exist_ok=True)
for own,expected in [('NNW_AUDIT_ROOTS.json','NLX_AUDIT_ROOTS.json'),('NNW_AUDIT_MODULES.json','NLX_AUDIT_MODULES.json')]:
 (w/expected).write_bytes((b/own).read_bytes())
os.chdir(w)
os.execv(str(p),[str(p),'proof0'])
