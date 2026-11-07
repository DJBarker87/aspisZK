"""Eight tiny symbolic bit-position windows; no native validation or recurrence reduction."""
from pathlib import Path
import argparse,json,hashlib
E=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args();out={}
items=', '.join('v '+str(i) for i in range(8))
out['NMX_R3_RawWord64Defs.lean']=f'''import Aeneas
set_option autoImplicit false
namespace NMX_R3_RawWord64Defs
def encoded (v : Fin 8 → BitVec 8) : BitVec 64 := BitVec.fromLEBytes [{items}]
def folded (v : Fin 8 → BitVec 8) : BitVec 64 :=
 [{items}].foldr (fun x acc => (acc <<< 8) ||| x.setWidth 64) 0
end NMX_R3_RawWord64Defs
'''
for k in range(8):
 positions=' ∨ '.join('i = '+str(j) for j in range(8*k,8*k+8))
 out[f'NMX_R3_RawWord64Byte{k}.lean']=f'''import NMX_R3_RawWord64Defs
set_option autoImplicit false
namespace NMX_R3_RawWord64Byte{k}
open NMX_R3_RawWord64Defs
theorem value (v : Fin 8 → BitVec 8) (i : Nat) (lo : {8*k} ≤ i) (hi : i < {8*k+8}) :
 (encoded v).getLsbD i = (folded v).getLsbD i := by
 have positions : {positions} := by omega
 rcases positions with {' | '.join(['rfl']*8)} <;>
  simp [encoded, folded, BitVec.fromLEBytes, BitVec.getLsbD_or,
   BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_of_ge]
#print axioms value
end NMX_R3_RawWord64Byte{k}
'''
s=''.join(f'import NMX_R3_RawWord64Byte{k}\n' for k in range(8))+'''set_option autoImplicit false
namespace NMX_R3_RawWord64
open NMX_R3_RawWord64Defs
theorem value (v : Fin 8 → BitVec 8) : encoded v = folded v := by
 apply BitVec.eq_of_getLsbD_eq
 intro i hi
'''
for k in range(7):s+=f' by_cases h{k} : i < {8*k+8}\n · exact NMX_R3_RawWord64Byte{k}.value v i (by omega) h{k}\n'
s+=' exact NMX_R3_RawWord64Byte7.value v i (by omega) hi\n#print axioms value\nend NMX_R3_RawWord64\n';out['NMX_R3_RawWord64.lean']=s
for name,s in out.items():
 if a.check:assert (E/name).read_text()==s,name
 else:(E/name).write_text(s)
manifest={name:hashlib.sha256(s.encode()).hexdigest() for name,s in out.items()}
if not a.check:(E/'NMX_R3_WORD64_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
else:assert json.loads((E/'NMX_R3_WORD64_MANIFEST.json').read_text())==manifest
print(json.dumps({'check':a.check,'modules':len(out),'method':'symbolic bit extensionality in eight constant-size windows'}))
