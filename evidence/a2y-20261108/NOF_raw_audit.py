"""Raw ax2 walk of the NOF roots with ledger30's pinned walker (read-only use)."""
from pathlib import Path
import json,hashlib,subprocess,sys,os
walker=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NNM_20261111/NNM_native/NNM_ProofDriver')
assert hashlib.sha256(walker.read_bytes()).hexdigest()=='46ee271b392729449147b978830b474e3fa4ecba2b45e03ad13c02490ba6ca3c'
out=Path.cwd()/'NOF_audit';out.mkdir(exist_ok=True);os.chdir(out)
roots=['AspisR1.NOF_A2Field.field','AspisR1.NOF_Tx2Op11.tx2Op11','AspisR1.NOF_CommonConverse.common',
 'AspisR1.NOF_PowersAssociation.source','AspisR1.NOF_A2Field.sdk_at_slot','AspisR1.NOF_A2Field.reserved_at']
Path('NLX_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=[roots])))
Path('NLX_AUDIT_MODULES.json').write_text(json.dumps([['NOF_FinalCombined']]))
r=subprocess.run([str(walker),'proof0']);sys.exit(r.returncode)
