"""Copy canonical reference definitions only; record exact getter stop extension."""
from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent;R=E.parent/'rowspec-lead-20261107'
records=[]
for row,imp in [('234','NMS_GeneralGetters'),('233','NMS_CloneRef234'),('242','NMS_CloneRef233'),('241','NMS_CloneRef242')]:
 src=(R/f'RSL_TX2_{row}.lean').read_text()
 if row=='234': start=src.index('/-- Immutable-deployment branch');end=src.index('/-- Own-input domain: none.')
 elif row=='233':start=src.index('/-- Body after');end=src.index('/-- Own-input domain: none.')
 elif row=='242':start=src.index('def Ref ');end=src.index('/-- Own-input domain: none.')
 else:start=src.index('def Ref ');end=src.index('/-- (D1) snapshot consistency.')
 body=src[start:end]
 original=body
 body=re.sub(r'RS\.ofExcept ([\w.]+)\.data',r'NMS_GeneralGetters.data \1',body)
 body=body.replace('RS.ofExcept (verifierCheckpoint v a.verifier_program false)',
    'NMS_GeneralGetters.checkpoint v a.verifier_program false')
 body=body.replace('TX2_234.Ref L D','NMS_CloneRef234.Ref L D')
 body=body.replace('TX2_233.Ref L D','NMS_CloneRef233.Ref L D')
 body=body.replace('TX2_242.Ref L D','NMS_CloneRef242.Ref L D')
 # Same canonical argument/return carriers and domains; only getter stops
 # are extended. In 241 V2Lib remains universally parameterized.
 extra=''
 if row=='241':extra='open RSL.TX2_241\n'
 s=f'''import {imp}
set_option autoImplicit false
namespace NMS_CloneRef{row}
open RSL RSL.TX2_{row}
{extra}
/- Canonical RSL reference with explicit general ProgramError clone stops.
Only getter interpretation and recursively corrected child references differ.
No normal result, payload, ordered effect, Box or original input is erased. -/
'''+body+f'\nend NMS_CloneRef{row}\n'
 # Add canonical type modules if the new dependency chain does not contain it.
 s=f'import RSL_TX2_{row}\n'+s
 (E/f'NMS_CloneRef{row}.lean').write_text(s)
 records.append(dict(row='TX2:'+row,canonical_file=f'RSL_TX2_{row}.lean',canonical_slice_sha256=hashlib.sha256(original.encode()).hexdigest(),replacement_slice_sha256=hashlib.sha256(body.encode()).hexdigest(),changes='RS.ofExcept account.data -> NMS_GeneralGetters.data; verifierCheckpoint -> source-ordered cloned-length guard; recursively use corrected child refs',new_domain=False,new_trust=False))
(E/'NMS_CLONE_REFERENCE_DIFF.json').write_text(json.dumps(records,indent=1)+'\n')
