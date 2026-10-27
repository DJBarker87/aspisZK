"""Small descriptor chunks, never field evaluation. --check validates all outputs."""
from pathlib import Path
import re,sys,json,hashlib
R=Path(__file__).resolve().parents[2];O=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=Path(__file__).parent
p=R/'crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal_constants.rs'
raw=p.read_text();pat=r'CompiledPoolV1PairForestLink \{ tag: (\d+), weight_kind: (\d+), weight_level: (\d+), producer: CompiledPoolV1PairForestEndpoint \{ row: (\d+), slot: (\d+), pattern: (\d+) \}, consumer: CompiledPoolV1PairForestEndpoint \{ row: (\d+), slot: (\d+), pattern: (\d+) \} \}'
links=[tuple(map(int,m)) for m in re.findall(pat,raw)];assert len(links)==136
masks=list(map(int,re.search(r'ACTIVE_ROW_MASKS: \[u16; 64\] = \[([^]]+)\]',raw)[1].split(',')))
for a in links:
 for row in (a[3],a[6]):assert masks[row//16]>> (row%16)&1

def literal(a):return f'⟨{a[0]}, {a[1]}, {a[2]}, ⟨{a[3]}, {a[4]}, {a[5]}⟩, ⟨{a[6]}, {a[7]}, {a[8]}⟩⟩'
def put(name,s):
 p=O/(name+'.lean')
 if '--check' in sys.argv:assert p.read_text()==s,str(p)
 else:p.write_text(s)
for n in range(34):
 name=f'PV_Inv_ActiveChunk{n:02}'
 s=f'''import R0P.Copy
set_option autoImplicit false
namespace R1Z.{name}
open R0P
/-- Generated terminal descriptor snapshot, entries {4*n}..{4*n+3}.
Native enumeration association remains P_registry; this is its model side. -/
def links : List CopyLink := [
  '''+',\n  '.join(map(literal,links[n*4:n*4+4]))+'''
]

theorem active (l : CopyLink) (hl : l ∈ links) :
    CopyActiveRow l.producer.row ∧ CopyActiveRow l.consumer.row := by
  simp only [links,List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl
  all_goals constructor <;> rfl

theorem tag_bound (l : CopyLink) (hl : l ∈ links) : l.tag < 2147483647 := by
  simp only [links,List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl <;> decide

#print axioms active
#print axioms tag_bound
'''+f'end R1Z.{name}\n'
 put(name,s)
s='\n'.join(f'import R1Z.PV_Inv_ActiveChunk{n:02}' for n in range(34))+'''
set_option autoImplicit false
namespace R1Z.PV_Inv_ActiveRegistry
open R0P
'''
s+='\ndef chunks : List CopyLink :=\n  '+' ++\n  '.join(f'PV_Inv_ActiveChunk{n:02}.links' for n in range(34))+'\n'
s+='''
/-- Literal descriptor equality only: no field computation, no native-enumerator claim. -/
theorem exact_table : chunks = copyLinks := by rfl

theorem active (l : CopyLink) (hl : l ∈ copyLinks) :
    CopyActiveRow l.producer.row ∧ CopyActiveRow l.consumer.row := by
  rw [←exact_table] at hl
  simp only [chunks,List.mem_append] at hl
  rcases hl with '''+('('*32+'h0 | h1'+''.join(') | h'+str(n) for n in range(2,34)))+'\n'
for n in range(34):s+=f'  · exact PV_Inv_ActiveChunk{n:02}.active l h{n}\n'
s+='''
theorem tag_bound (l : CopyLink) (hl : l ∈ copyLinks) : l.tag < 2147483647 := by
  rw [←exact_table] at hl
  simp only [chunks,List.mem_append] at hl
  rcases hl with '''+('('*32+'h0 | h1'+''.join(') | h'+str(n) for n in range(2,34)))+'\n'
for n in range(34):s+=f'  · exact PV_Inv_ActiveChunk{n:02}.tag_bound l h{n}\n'
s+='''
#print axioms exact_table
#print axioms active
#print axioms tag_bound
end R1Z.PV_Inv_ActiveRegistry
''';put('PV_Inv_ActiveRegistry',s)
(E/'active-generation.json').write_text(json.dumps(dict(source=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),links=len(links),chunks=34,classification='terminal descriptor snapshot; native association P_registry remains open',check=True),indent=2)+'\n')
