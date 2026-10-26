from pathlib import Path
import re,sys,json,hashlib
R=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
manifest=[]
for i in range(10,22):
 mods=[f'JFn_Value{i:02}_{j}' for j in range(4)]
 vals=[f'SAQ_RecordDecode.fromRecord {m}.value' for m in mods]
 s=''.join(f'import {m}\n' for m in mods)+'import JFn_ArrayBuilder\n'
 mod=f'JFn_Values{i:02}'
 s+=f'''set_option autoImplicit false
noncomputable section
namespace AspisR1.{mod}
open Aeneas Aeneas.Std Result
open AspisR1Stage2 Port3_NativeQueryBody

def value : Array SAQ_WideABI.E 4#usize := Array.make 4#usize [{','.join(vals)}]

/-- The actual ordered op0 body, with each op21 call made on opening[672:800]. -/
theorem source (seed : Port3_NativeQueryBody.Ops) :
    (JFn_ArrayBuilder.ops seed).op0 4#usize
      (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (JFn_ArrayBuilder.ops seed))
      (JFo_Opening.value ⟨{i},by decide⟩)=ok value :=
  JFn_ArrayBuilder.source seed ⟨{i},by decide⟩ _ _ _ _
    {mods[0]}.source {mods[1]}.source {mods[2]}.source {mods[3]}.source

'''
 for j,m in enumerate(mods):
  ws=re.search(r' := packed ([^\n]+)',(R/f'lean/{m}.lean').read_text())[1]
  ns=[int(v) for v in re.findall(r'(\d+)#u32',ws)]
  pred=lambda xs:' ∧ '.join(f'{v}<2147483647' for v in xs)
  s+=f'''theorem canonical{j} : Port4C_QueryArithmetic.CanonE ({vals[j]}) := by
  change ({pred(ns[:4])}) ∧ ({pred(ns[4:])})
  omega
#print axioms canonical{j}

'''
 s+='''theorem canonical (j : Fin 4) :
    Port4C_QueryArithmetic.CanonE (value.val[j.val]'(by rw [value.property];exact j.isLt)) := by
  fin_cases j
'''
 for j in range(4):s+=f'  · exact canonical{j}\n'
 q=[93499,147529,216823,245899,209371,192317,65593,183859,193093,159813,132355,218094,178080,149624,166165,42158,179622,21248,63860,55377,185637,14297][i]
 s+=f'\ntheorem selected : Array.index_usize value {q%4}#usize=ok ({vals[q%4]}) := rfl\n#print axioms selected\n'
 s+='\n#print axioms source\n#print axioms canonical\n' 
 s+=f'end AspisR1.{mod}\nend\n'
 f=R/f'lean/{mod}.lean'
 if '--check' in sys.argv:assert f.read_text()==s,f
 else:f.write_text(s)
 manifest.append(dict(module=mod,source_sha256=hashlib.sha256(s.encode()).hexdigest()))
(P/'JFn_ARRAYS.json').write_text(json.dumps(manifest,indent=2)+'\n')
