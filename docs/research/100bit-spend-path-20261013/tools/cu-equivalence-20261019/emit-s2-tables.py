#!/usr/bin/env python3
"""Pin literal source tables and emit small, named classification certificates."""
from pathlib import Path
import argparse,ast,hashlib,json,re,subprocess
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
here=Path(__file__).resolve().parent;repo=here.parents[4];area=here.parents[1]
revision='39c2971dd16c95858a4cfd2c9ae35da052eacfa9'
sha=lambda b:hashlib.sha256(b).hexdigest()
pins={}
def read(path):
 raw=(repo/path).read_bytes()
 assert raw==subprocess.check_output(['git','-C',str(repo),'show',revision+':'+path])
 pins[path]=sha(raw);return raw.decode()
weights=read('crates/aspis-r1-cost-probe/src/weights.rs')
transport=read('crates/aspis-r1-cost-probe/src/transport.rs')
opening=read('crates/aspis-core/src/r0/opening.rs')
def table(text,name,length):
 match=re.search(r'\b'+name+r'\s*:\s*\[[^\]]+\]\s*=\s*(\[[^\]]+\])',text)
 assert match,name
 values=ast.literal_eval(match[1]);assert len(values)==length,name
 return values
groups=table(weights,'S2_INACTIVE_GROUPS',64);masks=table(weights,'S2_INACTIVE_MASKS',12)
active=table(opening,'COPY_ACTIVE_ROW_MASKS',64);tau=table(transport,'TAU',5)
fmt=lambda xs:'['+','.join(map(str,xs))+']'
header='set_option autoImplicit false\nnamespace AspisR1.CuSavingsS2Tables\n'
data='import Mathlib.Tactic.FinCases\nimport Mathlib.Data.Fintype.Fin\n\n'+header
for name,values in [('groups',groups),('masks',masks),('active',active),('tau',tau)]:
 data+=f'def {name} : List Nat := {fmt(values)}\n'
data+='''
def row (coefficient : Nat) : Nat :=
  (List.range 5).foldl (fun out d =>
    out ||| (((coefficient >>> (2*d)) &&& 3) <<< (2*(tau.getD d 0)))) 0

def inactive (coefficient : Nat) : Bool :=
  !((active.getD (row coefficient / 16) 0).testBit (row coefficient % 16))

def groupValue (j : Fin 64) : Nat := groups.getD j.val 0

theorem groupValue_lt (j : Fin 64) : groupValue j < 12 := by
  fin_cases j <;> decide

def group (j : Fin 64) : Fin 12 := ⟨groupValue j,groupValue_lt j⟩

def groupMask (g : Fin 12) (bit : Fin 16) : Bool :=
  (masks.getD g.val 0).testBit bit.val

theorem lengths : groups.length = 64 ∧ masks.length = 12 ∧ active.length = 64 ∧ tau.length = 5 := by
  decide

#print axioms groupValue_lt
#print axioms lengths
end AspisR1.CuSavingsS2Tables
'''
outputs={'CuSavingsS2TableData.lean':data}
first=[groups.index(g) for g in range(12)]
assert first==sorted(first) and len(set(masks))==12
order='import CuSavingsS2TableData\n\n'+header
order+=f'def firstPositions : List Nat := {fmt(first)}\n'
order+='''def first (g : Fin 12) : Nat := firstPositions.getD g.val 0

theorem masks_distinct : masks.Nodup := by decide

theorem first_lt (g : Fin 12) : first g < 64 := by
  fin_cases g <;> decide

theorem first_occurrence (g : Fin 12) :
    groupValue ⟨first g,first_lt g⟩ = g.val ∧
      ∀ j : Fin 64, j.val < first g → groupValue j ≠ g.val := by
  fin_cases g <;> decide

theorem first_order (g h : Fin 12) (hgh : g.val < h.val) : first g < first h := by
  fin_cases g <;> fin_cases h <;> simp_all [first,firstPositions]

#print axioms masks_distinct
#print axioms first_lt
#print axioms first_occurrence
#print axioms first_order
end AspisR1.CuSavingsS2Tables
'''
outputs['CuSavingsS2Order.lean']=order
chunks=[[0],*[list(range(start,min(start+8,64))) for start in range(1,64,8)]]
for i,blocks in enumerate(chunks):
 text='import CuSavingsS2TableData\n\n'+header
 for j in blocks:
  text+=f'''theorem block_{j} (bit : Fin 16) :
    row (16*{j}+bit.val) < 1024 ∧
      groupMask (group ⟨{j},by decide⟩) bit = inactive (16*{j}+bit.val) := by
  fin_cases bit <;> decide

'''
 for j in blocks:text+=f'#print axioms block_{j}\n'
 text+='end AspisR1.CuSavingsS2Tables\n'
 outputs[f'CuSavingsS2TableChunk{i}.lean']=text
final='import CuSavingsGroups\n'+''.join(f'import CuSavingsS2TableChunk{i}\n' for i in range(len(chunks)))+'\n'+header
final+='''theorem table_correct (j : Fin 64) (bit : Fin 16) :
    row (16*j.val+bit.val) < 1024 ∧
      groupMask (group j) bit = inactive (16*j.val+bit.val) := by
  fin_cases j
'''
for j in range(64):final+=f'  · exact block_{j} bit\n'
final+='''
open scoped BigOperators
theorem grouped_inactive_eq {R : Type} [Semiring R]
    (coefficient : Fin 64 → R) (low : Fin 16 → R) :
    CuSavingsGroups.grouped group coefficient (fun g => CuSavingsGroups.maskWeight (groupMask g) low) =
      ∑ j, coefficient j * CuSavingsGroups.maskWeight (fun bit => inactive (16*j.val+bit.val)) low := by
  exact CuSavingsGroups.grouped_mask_eq group coefficient groupMask
    (fun j bit => inactive (16*j.val+bit.val)) low (fun j bit => (table_correct j bit).2)

#print axioms table_correct
#print axioms grouped_inactive_eq
end AspisR1.CuSavingsS2Tables
'''
outputs['CuSavingsS2Tables.lean']=final
manifest=dict(source_revision=revision,source_sha256=pins,source_tables=dict(groups=groups,masks=masks,active=active,tau=tau,first_positions=first),
 generated_sha256={name:sha(text.encode()) for name,text in outputs.items()},
 preflight_order=['Generic regrouping theorem','Table data/bounds','Chunk0 (one block, 16 cells)','Other small chunks','Table/grouped identity bridge'],
 exceptional_shapes='No generated recurrences or large numerals: each named block checks only sixteen ten-bit row classifications. No native_decide.',
 source_binding='Nat model of the exact five-iteration Variant::row loop and inactive bit test. Array lengths, all group indices and all 1024 row bounds are explicit certificate goals. Extracted machine loop/field binding remains required.')
for name,text in outputs.items():
 p=area/'lean'/name
 if a.check:assert p.read_text()==text,name
 else:p.write_text(text)
p=here/'s2-table-pins.json';text=json.dumps(manifest,indent=2)+'\n'
if a.check:assert p.read_text()==text
else:p.write_text(text)
print(json.dumps(dict(check=a.check,modules=len(outputs),blocks=64,cells=1024)))
