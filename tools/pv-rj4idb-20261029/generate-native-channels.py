"""Symbolic channel homomorphisms; no concrete recurrence or numeral reduction."""
from pathlib import Path
import sys
pairs=[('files','nativeFiles'),('json','nativeJSON'),('stdout','nativeStdout'),('diagnostics2','nativeDiag2'),('diagnostics3','nativeDiag3'),('counts','nativeCounts'),('times','nativeTimes'),('oracle','nativeOracle'),('rejections','nativeRejections'),('sideChannels','nativeSide')]
s='''import PV_RJ4IDB_NativeTrace
set_option autoImplicit false
namespace PV_RJ4IDB
'''
for m,n in pairs:
 s+=f'''
theorem {n}_translation (es : List NativeEvent) :
 {m} (es.map translateEvent) = {n} es := by
 induction es with
 | nil => rfl
 | cons e es ih =>
   cases e <;> simp only [List.map_cons,{m},{n},List.filterMap_cons,translateEvent,ih]
#print axioms {n}_translation
'''
s+='end PV_RJ4IDB\n';p=Path('lean/PV_RJ4IDB_NativeChannels.lean')
if '--check' in sys.argv:assert p.read_text()==s;print('native channel generator check passed')
else:p.write_text(s)
