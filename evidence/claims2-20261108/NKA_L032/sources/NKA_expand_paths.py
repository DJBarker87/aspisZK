from pathlib import Path
import json
B=Path(__file__).resolve().parent
roots=json.loads((B/'NKA_PATHS.json').read_text());extra=json.loads((B/'NKA_NJW_PATHS.json').read_text());old=len(roots)
for root in extra:
 if root not in roots:roots.append(root)
(B/'NKA_PATHS.json').write_text(json.dumps(roots,indent=2))
print('NKA appended ledger dependency roots:',len(roots)-old)
