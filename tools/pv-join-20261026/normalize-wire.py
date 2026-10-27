# Retained initial-stage generator. Final sources include reviewed proof corrections.
raise SystemExit('Retired draft generator; use the pinned final source files and combined-audit-manifest.json')
from pathlib import Path
import json,re
r=Path(__file__).resolve().parents[2];p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z';e=r/'evidence/pv-join-20261026/wire'
items=json.loads((e/'operations.json').read_text());fields=(r/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullExternalFuns.lean').read_text()
def binders(s):
 out=[];depth=0;beg=0
 for i,c in enumerate(s):
  if c in '({':
   if depth==0:beg=i
   depth+=1
  elif c in ')}':
   depth-=1
   if depth==0:out.append((s[beg],s[beg+1:i].split(':',1)[0].strip().split()))
 return out
for x in items:
 op=x['op'];s=re.search(r'^  op'+str(op)+r'\b([\s\S]*?)(?=^  op\d+\b|\Z)',fields,re.M)[1].strip()
 depth=0
 for i,c in enumerate(s):
  if c in '({[':depth+=1
  elif c in ')}]':depth-=1
  elif c==':' and depth==0:break
 head=s[:i].strip();typ=s[i+1:].strip()
 typ=('∀ '+head+', '+typ) if head else typ
 bs=binders(x['binders']);allnames=sum([a for _,a in bs],[]);explicit=sum([a for k,a in bs if k=='('],[])
 rhs=x['equation'].split(' =',1)[1].strip();extra='';proofargs=explicit[:]
 if op==225:
  extra='''section
variable [ProverRwFull.ExternalTypes]
-- The extracted projection ignores both payloads. These total adapters are
-- data allowed by its original theorem, not representation assumptions.
def transfer : Transfer → Raw.Transfer := fun _ =>
  ⟨Array.make 32#usize (List.replicate 32 0#u8),
   Array.make 32#usize (List.replicate 32 0#u8), 0#u64,
   Array.make 8#usize (List.replicate 8 0#u32),
   Array.make 8#usize (List.replicate 8 0#u32), 0#u32,
   Array.make 8#usize (List.replicate 8 0#u32),
   Array.make 8#usize (List.replicate 8 0#u32)⟩
def withdrawal : Withdrawal → Raw.Withdrawal := fun _ =>
  ⟨Array.make 32#usize (List.replicate 32 0#u8),
   Array.make 32#usize (List.replicate 32 0#u8), 0#u64,
   Array.make 8#usize (List.replicate 8 0#u32),
   Array.make 8#usize (List.replicate 8 0#u32), 0#u32, 0#u32,
   Array.make 32#usize (List.replicate 32 0#u8),
   Array.make 8#usize (List.replicate 8 0#u32)⟩
end
'''
  bs=bs[2:];allnames=['p'];proofargs=['transfer','withdrawal','p']
 lam=' '.join(('{'+ ' '.join(a)+'}') if k=='{' else ' '.join(a) for k,a in bs)
 body=f'''import {x['module']}
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Entry{op}
open {x['opens']}
'''+extra+f'''/-- Source-normal form for exactly this callback, including all Result cases. -/
def source (base : ProverRwFull.ExternalTypes) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    {typ} :=
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  '''+('fun '+lam+' => ' if lam else '')+rhs+f'''
theorem equation (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    @ProverRwFull.ExternalFuns.op{op} _ (PV_Join_Wire_Selection.selected base ops) = source base := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
'''+('  funext '+' '.join(allnames)+'\n' if allnames else '')+'  exact '+x['theorem']+' base ops'+(' '+' '.join(proofargs) if proofargs else '')+f'''
#print axioms equation
end R1Z.PV_Join_Wire_Entry{op}
'''
 (p/f'PV_Join_Wire_Entry{op}.lean').write_text(body)
print('Generated',len(items),'source function equalities')
