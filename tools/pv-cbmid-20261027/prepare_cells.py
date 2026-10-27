"""Split exact extracted cell functions and apply the checked symbolic push lemma.
No concrete complete-vector reduction is emitted. Native equality remains separate.
"""
from pathlib import Path
import re,json,hashlib,sys
root=Path(__file__).resolve().parents[2]; evidence=root/'evidence/pv-cbmid-20261027'
src=evidence/'aeneas-op132ref-001/Funs.lean';text=src.read_text()
namespace='PV_CBM_Op132refRaw';assert f'namespace {namespace}' in text
matches=list(re.finditer(r'/-- \[pv_cbm_source::reference::(\w+)\]',text))
sections={}
for i,m in enumerate(matches):
 end=matches[i+1].start() if i+1<len(matches) else text.index('\nend '+namespace,m.start())
 sections[m.group(1)]=text[m.start():end].replace(namespace,'PV_CBM_CellsRaw').strip()
manifest=json.loads((evidence/'REFERENCE-CANDIDATE.json').read_text());cells=manifest['cells'];sizes=manifest['chunk_sizes'];assert sum(sizes)==len(cells)==3803
assert all('cells_chunk_'+str(i) in sections for i in range(len(sizes)))
# The original TraceCell is the exact same two-field extracted Rust carrier.
types=(evidence/'aeneas-op132ref-001/Types.lean').read_text()
assert re.search(r'structure aspis_statement\.trace_v4\.TraceCell where\s+row : Std.U16\s+column : Std.U8',types)
base=root/'docs/research/v8-r0-zk-20261009/lean/R1Z';outputs={}
outputs['PV_CBM_CellTypes']='''import R1Z.PV_CBM_ReferenceTypes
import R1Z.ProverRwFullTypes
namespace PV_CBM_CellsRaw
abbrev aspis_statement.trace_v4.TraceCell := ProverRwFull.aspis_statement.trace_v4.TraceCell
abbrev aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1 :=
  PV_CBM_ReferenceRaw.aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1
end PV_CBM_CellsRaw
'''
pre='open Aeneas Aeneas.Std Result ControlFlow Error\n'
imports=[];offset=0
for i,size in enumerate(sizes):
 name=f'PV_CBM_CellChunk{i:02}';imports.append('import R1Z.'+name)
 literals=',\n    '.join('{row := '+str(r)+'#u16, column := '+str(c)+'#u8}' for r,c in cells[offset:offset+size]);offset+=size
 body='-- Exact Aeneas function; carrier aliases identify the same frozen Rust types.\n'
 body+='import R1Z.PV_CBM_CellTypes\nimport R1Z.PV_CBM_PushList\n'+pre+'namespace PV_CBM_CellsRaw\n'+sections['cells_chunk_'+str(i)]+'\nend PV_CBM_CellsRaw\n'
 body+=f'namespace R1Z.{name}\nset_option autoImplicit false\n'
 body+='def literals : List ProverRwFull.aspis_statement.trace_v4.TraceCell := [\n    '+literals+'\n  ]\n'
 body+=f'theorem length : literals.length = {size} := rfl\n'
 body+=f'theorem source (out : alloc.vec.Vec ProverRwFull.aspis_statement.trace_v4.TraceCell) :\n    PV_CBM_CellsRaw.reference.cells_chunk_{i} out = PV_CBM_PushList.pushList literals out := rfl\n'
 body+=f'theorem run (out : alloc.vec.Vec ProverRwFull.aspis_statement.trace_v4.TraceCell)\n    (hc : out.val.length + {size} ≤ 4096) :\n    ∃ result, PV_CBM_CellsRaw.reference.cells_chunk_{i} out = ok result ∧\n      result.val = out.val ++ literals := by\n  rw [source]\n  apply PV_CBM_PushList.pushList_spec\n  simpa only [length] using hc\n'
 body+='#print axioms length\n#print axioms source\n#print axioms run\nend R1Z.'+name+'\n'
 outputs[name]=body
outputs['PV_CBM_CellsReference']='\n'.join(imports)+'\n'+pre+'namespace PV_CBM_CellsRaw\n'+sections['cells']+'\n#print axioms reference.cells\nend PV_CBM_CellsRaw\n'
check='--check' in sys.argv
for name,s in outputs.items():
 p=base/(name+'.lean')
 if check:assert p.read_text()==s,name
 else:p.write_text(s)
record=dict(generator='tools/pv-cbmid-20261027/prepare_cells.py',input_sha256=hashlib.sha256(text.encode()).hexdigest(),cells=3803,chunks=len(sizes),max_chunk_size=max(sizes),named_symbolic_lemma='R1Z.PV_CBM_PushList.pushList_spec',status='owned reference certificate; shipped equality unproved',outputs={n:hashlib.sha256(s.encode()).hexdigest() for n,s in outputs.items()})
if check:assert json.loads((evidence/'CELL-CERTIFICATE.json').read_text())==record
else:(evidence/'CELL-CERTIFICATE.json').write_text(json.dumps(record,indent=2)+'\n')
print('CHECK' if check else 'GENERATED',len(outputs),'modules')
