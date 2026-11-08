"""Raw ax2 for only the four newly added equality proofs; reuse passing fixtures."""
from pathlib import Path
import json,hashlib,subprocess,sys
B=Path.cwd();P=B.parent/'NNM_20261111';walker=P/'NNM_native/NNM_ProofDriver'
assert hashlib.sha256(walker.read_bytes()).hexdigest()=='46ee271b392729449147b978830b474e3fa4ecba2b45e03ad13c02490ba6ca3c'
roots=['NNN_InstalledChecks.'+n for n in ['f344_same','f240_same','process_same','entry_same']]
(B/'NLX_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=[roots])))
(B/'NLX_AUDIT_MODULES.json').write_text(json.dumps([['NNN_COMBINED_IMPORT']]))
r=subprocess.run([str(walker),'proof0']);sys.exit(r.returncode)
