"""Generate symbolic ordered-store footprint laws; no concrete recurrence reduction."""
from pathlib import Path
import sys
P=Path('lean/PV_EVH_EntropyReturnFootprint.lean')
# Exact adopted store order: staging high/low, then interleaved returned halves.
rows=[
 ('stageFieldHigh','sp+176','sp+16',16),('stageFieldLow','sp+160','sp',16),
 ('stageSeedLow','sp+192','sp+32',16),('stageSeedHigh','sp+208','sp+48',16),
 ('stageMaskHigh','sp+144','mask sp+16',16),('stageMaskLow','sp+128','mask sp',16),
 ('returnSeedHigh','result sp+81','sp+48',16),
 ('returnMaskHigh','result sp+17','mask sp+16',16),
 ('returnMaskLow','result sp+1','mask sp',16),
 ('returnSeedLow','result sp+65','sp+32',16),
 ('returnFieldHigh','result sp+49','sp+16',16),
 ('returnFieldLow','result sp+33','sp',16),
 ('tag','result sp',None,1)]
names=[r[0] for r in rows]
args=lambda ns:'['+','.join(n+' sp w' for n in ns)+']'
text='''import PV_EVH_StackStores
import PV_EVH_EntropyCallerLayout
set_option autoImplicit false
namespace PV_EVH_EntropyReturnFootprint
open PV_EVH_StackZero (State)
open PV_EVH_StackStores (Store Outside run)
open PV_EVH_EntropyCallerLayout (mask result caller)

/-- Captured source/register values at the accepted branch of the adopted
artifact. These are physical memory laws, not an installed native family.
Source/ABI interpretation and all register/spill/L3 observations remain P.
No moved-from inner slot or staging byte is cleared by these stores. -/
'''
for n,d,s,z in rows:
 value='fun i => w.memory ('+s+'+i)' if s else 'fun _ => 0'
 text+=f'def {n} (sp : Nat) (w : State) : Store := ⟨{d},{z},{value}⟩\n'
text+='\ndef stores (sp : Nat) (w : State) : List Store :=\n  '+args(names)+'\n\ndef moved (sp : Nat) (w : State) : State := run (stores sp w) w\n\n'
def outside_tactic(later):
 if not later:return '  simp only [List.not_mem_nil] at ht\n'
 txt='  simp only [List.mem_cons,List.not_mem_nil,or_false] at ht\n'
 if len(later)>1:txt+='  rcases ht with '+' | '.join(['rfl']*len(later))+'\n'
 else:txt+='  subst t\n'
 txt+='  all_goals\n    simp only [Outside,'+','.join(names)+',result,mask,caller] at *\n    omega\n'
 return txt
for k,(n,d,s,z) in enumerate(rows):
 value='w.memory ('+s+'+i)' if s else '0'
 text+=f'theorem {n}_byte (sp : Nat) (w : State) (i : Nat) (hi : i < {z}) :\n    (moved sp w).memory ({d}+i) = {value} := by\n'
 text+='  apply PV_EVH_StackStores.selected '+args(names[:k])+' '+args(names[k+1:])+f' ({n} sp w) w i hi\n'
 text+='  intro t ht\n'+outside_tactic(names[k+1:])+'\n'
for name,p,hi in [('inner_residue','sp+i',128),('mask_residue','mask sp+i',32)]:
 text+=f'theorem {name} (sp : Nat) (w : State) (i : Nat) (hi : i < {hi}) :\n    (moved sp w).memory ({p}) = w.memory ({p}) := by\n'
 text+='  apply PV_EVH_StackStores.outside_all\n  intro t ht\n  change t ∈ '+args(names)+' at ht\n'
 text+=outside_tactic(names)+'\n' # fix indentation below
text+='''theorem outside_writes (sp p : Nat) (w : State)
    (hf : p < sp ∨ sp+232 ≤ p)
    (hr : p < result sp ∨ result sp+97 ≤ p) :
    (moved sp w).memory p = w.memory p := by
  apply PV_EVH_StackStores.outside_all
  intro t ht
  change t ∈ '''+args(names)+''' at ht
'''
text+=outside_tactic(names)
text+='\n'+'\n'.join('#print axioms '+n+'_byte' for n in names)+'\n#print axioms inner_residue\n#print axioms mask_residue\n#print axioms outside_writes\nend PV_EVH_EntropyReturnFootprint\n'
if '--check' in sys.argv:assert P.read_text()==text
else:
 import json
 assert not any(json.loads(r.read_text()).get('accepted') and json.loads(r.read_text())['target']==P.stem for r in Path('evidence/pv-evh10-20261102').glob('receipt-*.json')),'accepted source immutable'
 assert not P.exists() or '--update-unaccepted' in sys.argv,'new module only'
 P.write_text(text)
print('PASS ordered return store generator',len(rows),'symbolic stores')
