"""Check native field-table coordinates against the existing complete projection."""
from pathlib import Path
import sys,re,json
E=Path(__file__).resolve().parent
sys.path.insert(0,str(E.parent/'slice-s-compose7-20261103'))
from NEU_bridge_checks import COMMON,PUBLIC

def field(receiver,expression):
 expression=expression.removesuffix('.0')
 chunks=re.split(r'\[([ijk])\]',expression)
 value=receiver+'.'+chunks[0]
 for n in range(1,len(chunks),2):
  value='(NEU_PublicProjections.get '+value+' '+chunks[n]+')'
  value+=chunks[n+1]
 return value+'.val'
rows=[]
expected=json.loads((E.parent/'slice-s-compose8-20261104/NEX_K133-shape.json').read_text())['fields']
for slot in range(26):
 if slot==0:transfer,withdrawal='1','2';rust='s.transition_kind() as u64'
 elif slot<16:
  transfer=withdrawal=field('c',COMMON[slot-1]);rust='s.common().'+COMMON[slot-1]+' as u64'
 elif slot<23:
  transfer=withdrawal=field('p',PUBLIC[slot-16]);rust='public.'+PUBLIC[slot-16]+' as u64'
 elif slot==23:transfer,withdrawal=field('p','recipient_commitment[i].0'),'0';rust='transfer recipient word; withdrawal0'
 elif slot==24:transfer,withdrawal='0',field('p','amount');rust='transfer0; withdrawal amount'
 else:transfer,withdrawal='0',field('p','destination_token_account[j]');rust='transfer0; withdrawal destination byte'
 name=f'NEY_Field{slot:02}'
 source=f'''import NEX_StatementExt
set_option autoImplicit false
noncomputable section
namespace {name}
open Aeneas Aeneas.Std
open AspisR1TerminalDecoder.pool_v1.pair_forest_terminal
abbrev Statement := PoolV1PairForestTerminalStatementV1

def expected (s : Statement) (i : Fin 8) (j : Fin 32) (k : Fin 20) : Nat :=
 match s with
 | .PrivateTransfer c p => {transfer}
 | .Withdrawal c p => {withdrawal}

/-- The observed frozen native field has this exact cohort coordinate. The
complete-record extensionality theorem is imported, never re-proved. -/
theorem alignment (s : Statement) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    NEX_StatementExt.project s ⟨{slot},by decide⟩ i j k = expected s i j k := by
  cases s <;> rfl
#print axioms alignment
end {name}
'''
 (E/(name+'.lean')).write_text(source)
 rows.append(dict(slot=slot,module=name,theorem=name+'.alignment',native_projection=expected[slot],transfer=transfer,withdrawal=withdrawal))
(E/'NEY_FIELD_ALIGNMENT_TABLE.json').write_text(json.dumps(rows,indent=1)+'\n')
