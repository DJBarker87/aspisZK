"""Emit source-shaped numeric recursion without unfolding UInt values."""
from pathlib import Path
import sys
r=Path(__file__).resolve().parents[2]
ks=['isize','i64','i32','i16','i8','usize','u64','u32','u16','u8']
s='''import R1Z.PDict_Typenum
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Numeric
open Aeneas Aeneas.Std Result ProverRwFull

'''
for i in range(141,161):
 k=ks[(i-141)%10];typ=k[0].upper()+k[1:];signed=k.startswith('i');Ty='I' if signed else 'U';cast='hcast' if signed else 'cast';field=k.upper() if i>=151 else 'to_'+k;bit='U8' if i>=151 else 'to_u8'
 s+=f'''def op{i} {{U B : Type}} (u : typenum.marker_traits.Unsigned U)
    (b : typenum.marker_traits.Bit B) : Result {typ} := do
  let digit ← b.{bit}
  let upper ← u.{field}
  let shifted ← Aeneas.Std.lift ({typ}.wrapping_shl upper 1#u32)
  Aeneas.Std.lift ((UScalar.{cast} .{typ} digit) ||| shifted)

'''
s+='''variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  { PDict_Typenum.selected ops with
'''+',\n'.join(f'    op{i} := @op{i}' for i in range(141,161))+' }\n\n'
for i in range(141,161):
 s+=f'''theorem op{i}_installed (ops : ExternalFuns) {{U B : Type}}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op{i} u b = op{i} u b := rfl

#print axioms op{i}_installed

'''
s+='''theorem bit_failure {U B : Type} (u : typenum.marker_traits.Unsigned U)
    (b : typenum.marker_traits.Bit B) (e : Error) (h : b.to_u8 = .fail e) :
    op150 u b = .fail e := by
  simp only [op150,h,bind_tc_fail]

#print axioms bit_failure
end R1Z.PDict_Numeric
'''

p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/PDict_Numeric.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
