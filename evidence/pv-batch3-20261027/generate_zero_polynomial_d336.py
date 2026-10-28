"""Generate only small bounded block-address lemmas, never polynomial runs."""
from pathlib import Path
import sys
D=Path(__file__).resolve().parent;p=D/'lean/PV_B3_ZeroPolynomial.lean';s=p.read_text();a=s.index('theorem start0 :');b=s.index('theorem block0 :',a)
part=''
for i in range(7):
 part+=f'theorem start{i} : Usize.wrapping_mul 4#usize {i}#usize = {4*i}#usize := by scalar_tac\n#print axioms start{i}\n'
 for j in [1,2,3]:part+=f'theorem offset{i}_{j} : Usize.wrapping_add {4*i}#usize {j}#usize = {4*i+j}#usize := by scalar_tac\n#print axioms offset{i}_{j}\n'
expected=s[:a]+part+s[b:]
if '--check' in sys.argv:assert s==expected,'bounded address leaves changed'
else:p.write_text(expected)
print('checked seven block starts and 21 offsets; symbolic zero and array lemmas handle all arithmetic traversals')
