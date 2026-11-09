"""Raw ax2 walk of the NOQ A1 field with ledger30's pinned walker (read-only use; same binary as NOF_ L014/L018)."""
from pathlib import Path
import json,hashlib,subprocess,sys,os
walker=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NNM_20261111/NNM_native/NNM_ProofDriver')
assert hashlib.sha256(walker.read_bytes()).hexdigest()=='46ee271b392729449147b978830b474e3fa4ecba2b45e03ad13c02490ba6ca3c'
out=Path.cwd()/'NOQ_audit';out.mkdir(exist_ok=True);os.chdir(out)
roots=['AspisR1.NOQ_FinalCombined.field']
Path('NLX_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=[roots])))
Path('NLX_AUDIT_MODULES.json').write_text(json.dumps([['NOQ_FinalCombined']]))
r=subprocess.run([str(walker),'proof0']);sys.exit(r.returncode)
