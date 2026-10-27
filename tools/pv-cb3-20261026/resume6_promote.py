"""Reproduce the supported op258 reference adapter; --check never writes Lean."""
from pathlib import Path
import hashlib,json,sys
root=Path(__file__).resolve().parents[2];e=root/'evidence/pv-cb3-20261026'
p=e/'aeneas-source-op258-reference-resume6/Funs.lean.txt';s=p.read_text()
s=s.replace('import PVCB3Op258Reference.Types','import R1Z.ProverRwFullExternalFuns')
s=s.replace('namespace PV_CB3_Op258Reference','namespace R1Z.PV_CB3_Op258Ref').replace('end PV_CB3_Op258Reference','end R1Z.PV_CB3_Op258Ref')
s=s.replace('namespace R1Z.PV_CB3_Op258Ref','namespace R1Z.PV_CB3_Op258Ref\nabbrev aspis_core.field.M31 := ProverRwFull.aspis_core.field.M31\nabbrev aspis_core.field.CM31 := ProverRwFull.aspis_core.field.CM31\nabbrev aspis_core.field.QM31 := ProverRwFull.aspis_core.field.QM31',1)
assert s.count('4#i32')==1;s=s.replace('4#i32','4#u32')
assert s.count('Std.U16.wrapping_shl 1#u16 i3')==1
s=s.replace('Std.U16.wrapping_shl 1#u16 i3','Std.U16.wrapping_shl 1#u16 (UScalar.cast .U32 i3)')
target=root/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_CB3_Op258Ref.lean'
r=dict(original_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),promoted_sha256=hashlib.sha256(s.encode()).hexdigest(),path=str(target.relative_to(root)),matches=target.exists() and target.read_text()==s,source_extraction='aeneas-source-op258-reference-resume6/collected-receipt.json',transformations=['namespace/import binding','M31/CM31/QM31 structural aliases to the existing extracted carrier','4#i32 to 4#u32, equal numeric values proved by PV_CB3_MaskCast.literal_four','usize shift count narrowed to u32, exactness proved by PV_CB3_MaskCast.cast_value'],exceptional_cells='No concrete arithmetic recurrence cells generated; bounds and shift shape are symbolic lemmas.')
if '--check' in sys.argv:
 assert r['matches'],r
else:target.write_text(s)
(e/'RESUME6_PROMOTION_CHECK.json').write_text(json.dumps(r,indent=2)+'\n')
print('op258 reference promotion check:',r['matches'])
