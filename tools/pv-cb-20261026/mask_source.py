"""Prepare mask control rebind; fresh current-source extraction audit remains required."""
from pathlib import Path
import re,json,hashlib,sys
root=Path(__file__).resolve().parents[2]
src=root/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwSuccessMaskSource.lean'
s=src.read_text();starts=list(re.finditer(r'^def\s+([\w.]+)',s,re.M));blocks=[];pins={}
for i,m in enumerate(starts):
 n=m[1]
 if not n.startswith('state_only_hiding.'):continue
 end=starts[i+1].start() if i+1<len(starts) else s.index('\nend R1Z.')
 b=s[m.start():end].strip()
 b=re.sub(r'(?<![\w.])field\.', 'ProverRwP7CurrentFieldSource.aspis_core.field.', b)
 blocks.append(b);pins[n]=hashlib.sha256(s[m.start():end].strip().encode()).hexdigest()
p=root/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_CB_MaskSource.lean'
out='''import R1Z.ProverRwP7CurrentFieldSource
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_MaskSource
open Aeneas Aeneas.Std Result ControlFlow Error
-- Prepared control rebind. Fresh current-source extraction comparison is pending.
'''+ '\n\n'.join(blocks)+'''
#print axioms state_only_hiding.state_only_selected_mask_value
end R1Z.PV_CB_MaskSource
'''
if '--check' in sys.argv:assert p.read_text()==out
else:
 p.write_text(out)
 (root/'evidence/pv-cb-20261026/mask-rebind.json').write_text(json.dumps(dict(status='PREPARED; not a current-source extraction theorem',source=str(src.relative_to(root)),source_sha256=hashlib.sha256(s.encode()).hexdigest(),blocks=pins,output_sha256=hashlib.sha256(out.encode()).hexdigest(),change='state_only_hiding control bodies retained; nominal field method/type references rebound to checked current wrapping API; fresh current-source extraction audit still pending'),indent=2)+'\n')
