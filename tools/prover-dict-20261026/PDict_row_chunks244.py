"""Named128-cell row-table chunks, avoiding a1024-cell length reduction.

Every chunk is checked independently. This is source/literal association, not
backend modification or an assumed native equivalence.
"""
from pathlib import Path
import hashlib, json, re, sys
root=Path(__file__).resolve().parents[2]
e=root/'docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026/world244'
dest=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'
values=list(map(int,(e/'frozen-order244.txt').read_text().split()))
assert len(values)==1024 and sorted(values)==list(range(1024))
emitted=(e/'emission-owned/Funs.lean.txt').read_text()
raw=emitted.split('def row.ORDER :',1)[1].split('\n/--',1)[0]
cells=list(map(int,re.findall(r'(\d+)#u16',raw)))
assert cells==values, 'literal table differs from frozen export'
for i in range(8):
    chunk=values[128*i:128*(i+1)]
    name=f'PDict_RowChunk244_{i}'
    text='import R1Z.PDict_RowBounds244\nset_option autoImplicit false\nnamespace R1Z.'+name+'\nopen Aeneas Aeneas.Std\n'
    for part in range(8):
        segment=chunk[part*16:(part+1)*16]
        text+=f'def part_{part} : List U16 := ['+', '.join(f'{v}#u16' for v in segment)+']\n'
        text+=f'theorem part_{part}_length : part_{part}.length = 16 := rfl\n'
        text+=f'theorem part_{part}_bound : ∀ x ∈ part_{part}, x.val < 1024 := by\n  intro x member\n'
        text+=f'  simp only [part_{part},List.mem_cons,List.not_mem_nil,or_false] at member\n'
        text+='  rcases member with '+' | '.join(['rfl']*16)+'\n  all_goals scalar_tac\n'
        text+=f'#print axioms part_{part}_length\n#print axioms part_{part}_bound\n'
    text+='def values : List U16 := '+' ++ '.join(f'part_{j}' for j in range(8))+'\n'
    text+='theorem length : values.length = 128 := by\n  simp only [values,List.length_append,'+', '.join(f'part_{j}_length' for j in range(8))+']\n'
    expr='part_0_bound'
    for part in range(1,8):
        expr=f'(PDict_RowBounds244.append_bound _ _ {expr} part_{part}_bound)'
    text+='theorem bound : ∀ x ∈ values, x.val < 1024 :=\n  '+expr+'\n'
    text+='#print axioms length\n#print axioms bound\nend R1Z.'+name+'\n'
    p=dest/(name+'.lean')
    if '--check' in sys.argv: assert p.read_text()==text
    elif not p.exists() or p.read_text()!=text: p.write_text(text)
(e/'row-chunks244.json').write_text(json.dumps(dict(chunks=8,cells_per_chunk=128,
    literal_identity='Parsed every emitted U16 cell and matched it in order to the frozen Rust export; chunking changes only List append association.',
    source_sha256={f'PDict_RowChunk244_{i}':hashlib.sha256((dest/f'PDict_RowChunk244_{i}.lean').read_bytes()).hexdigest() for i in range(8)},
    formal_claim='Each chunk uses eight16-cell named length/bound certificates, avoiding the rejected128-way rcases; aggregate consumes these without flat-list normalization.'),indent=2)+'\n')
