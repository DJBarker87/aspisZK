"""Permanent scalar-only certificate preflight for the zero mask witness.
Never reduce an entire scatter/Horner run. Generate named table, bit and cast
leaves; traverse using symbolic zero/index/update lemmas in the manual tail.
"""
from pathlib import Path
import re,sys
D=Path(__file__).resolve().parent;R=D.parents[1];p=D/'lean/PV_B3_ZeroMask117.lean'
rust=(R/'crates/aspis-prover/src/host_arithmetic.rs').read_text();s=p.read_text();a=s.index('theorem factor0 :');b=s.index('theorem selected :',a)
text=''
for prefix,table in [('factor','FACTOR_EXPONENTS'),('maskfactor','MASK_ONLY_FACTOR_EXPONENTS')]:
 expr=rust.split('const '+table+':',1)[1].split('=',1)[1].split(';',1)[0]
 values=list(map(int,re.findall(r'\d+',expr)))
 assert len(values)==(16 if prefix=='factor'else 10)
 for i,v in enumerate(values):
  text+=f'theorem {prefix}{i} : Array.index_usize host_arithmetic.{table} {i}#usize = ok {v}#u8 := by\n  unfold host_arithmetic.{table}\n  rfl\n#print axioms {prefix}{i}\n'
for i in range(16):
 text+=f'theorem and3_{i} : ({i}#usize &&& 3#usize) = {i%4}#usize := by with_unfolding_all rfl\n#print axioms and3_{i}\n'
values=sorted(set([0,2,4,6,8,10,12,14,16,18,20,22,24,26,13,25,1,3,5,7,9,11,15,17,19,21]))
for v in values:text+=f'theorem cast{v} : UScalar.cast .Usize {v}#u8 = {v}#usize := by scalar_tac\n#print axioms cast{v}\n'
expected=s[:a]+text+s[b:]
if '--check' in sys.argv:assert expected==s,'scalar leaves differ from generator'
else:p.write_text(expected)
print('checked 26 table projections, 16 small bit operations, 26 bounded casts; no full recurrence normalization')
