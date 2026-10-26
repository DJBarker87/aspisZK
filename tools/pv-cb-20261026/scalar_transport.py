"""Generate a field-wise bijection for the extracted CodeField callback record."""
from pathlib import Path
import sys
n=sys.argv[1]
root=Path(__file__).resolve().parents[2]
p=root/f'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_CB_Op{n}Types.lean'
s=p.read_text();assert 'structure aspis_core.r0.scalar.CodeField (Self : Type) where' in s
fields=['ZERO','ONE','coremarkerCopyInst','corecmpEqInst','from_m31','add','sub','neg','mul','try_inv']
block=s.split('structure aspis_core.r0.scalar.CodeField (Self : Type) where')[1].split('/--')[0].split('\nend ')[0]
assert [line.strip().split(' : ')[0] for line in block.splitlines() if ' : ' in line]==fields
assign='\n'.join('  '+f+' := x.'+f for f in fields)
out=f'''import R1Z.PV_CB_Op{n}Types
import R1Z.PV_CB_State
set_option autoImplicit false
namespace R1Z.PV_CB_Op{n}Transport
abbrev Native (E : Type) := ProverRwFull.aspis_core.r0.scalar.CodeField E
abbrev Raw (E : Type) := PV_CB_ShippedOp{n}.aspis_core.r0.scalar.CodeField E
def encode {{E : Type}} (x : Native E) : Raw E := {{
{assign}
}}
def decode {{E : Type}} (x : Raw E) : Native E := {{
{assign}
}}
theorem native_roundtrip {{E : Type}} (x : Native E) : decode (encode x) = x := by cases x; rfl
theorem extracted_roundtrip {{E : Type}} (x : Raw E) : encode (decode x) = x := by cases x; rfl
#print axioms native_roundtrip
#print axioms extracted_roundtrip
end R1Z.PV_CB_Op{n}Transport
'''
p.with_name(f'PV_CB_Op{n}Transport.lean').write_text(out)
