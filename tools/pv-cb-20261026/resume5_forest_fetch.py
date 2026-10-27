"""Normalize a fresh forest tuple helper only after exact shared-source checks.
Never substitutes an opaque compressor or changes a generated source body.
"""
from pathlib import Path
import subprocess,json,hashlib,re
root=Path(__file__).resolve().parents[2];ev=root/'evidence/pv-cb-20261026';lean=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'
base='/home/dombarker/project-offloads/codex-pv-cb-20261026'
raw={}
for part in ['Types','Funs','FunsExternal_Template']:
 raw[part]=subprocess.check_output(['ssh','dombarker@100.108.41.90','cat',base+'/shipped-op223Forest-generated/'+part+'.lean'],text=True)
old_types=(ev/'aeneas-source-op223Tuple-resume5-producer-r02/Types.lean.txt').read_text()
old_funs=(ev/'aeneas-source-op223Tuple-resume5-producer-r02/Funs.lean.txt').read_text()
old_external=(ev/'aeneas-source-op223Tuple-resume5-producer-r02/FunsExternal_Template.lean.txt').read_text()
rename=lambda s:s.replace('PV_CB_ShippedOp223Forest','PV_CB_ShippedOp223Tuple').replace('PVCBShippedOp223Forest','PVCBShippedOp223Tuple')
# Charon reordered the independent TraceCell and Bank declarations.
# Require every complete declaration block, header and footer byte-identical.
def type_blocks(s):
 return sorted(s.split('/-- '))
assert type_blocks(rename(raw['Types']))==type_blocks(old_types),'Actual Rust type declarations differ beyond ordering; use explicit carriers' 
assert rename(raw['FunsExternal_Template'])==old_external,'Opaque interface differs; do not invent a replacement'
s=rename(raw['Funs']);removed=[]
# Four exact shared primitive declarations from the same Rust source and config.
markers=['/-- [aspis_core::field::P]', '/-- [aspis_core::field::{aspis_core::field::M31}::ZERO]', '/-- [aspis_core::field::{aspis_core::field::M31}::sub]:', '/-- [aspis_statement::poseidon2::MERKLE_NODE_COMPRESSION_V3_TWEAK]']
for marker in markers:
 def block(text):
  a=text.index(marker);b=text.find('\n/-- ',a+4)
  if b<0:b=text.index('\nend PV_CB_ShippedOp223Tuple',a)
  return text[a:b]
 actual=block(s);expected=block(old_funs)
 assert actual==expected,'Shared primitive differs: '+marker
 removed.append({'marker':marker,'sha256':hashlib.sha256(actual.encode()).hexdigest()})
 s=s.replace(actual,'',1)
s=s.replace('import PVCBShippedOp223Tuple.Types\nimport PVCBShippedOp223Tuple.FunsExternal','import R1Z.PV_CB_Op223TupleProducerFuns')
s=s.replace('namespace PV_CB_ShippedOp223Tuple','namespace PV_CB_ShippedOp223Tuple\nvariable [ExternalFuns]',1)
s+='\n#print axioms PV_CB_ShippedOp223Tuple.pool_v1.pair_forest_trace.tuple_cells\n#print axioms PV_CB_ShippedOp223Tuple.pool_v1.pair_forest_trace.tuple_cells_loop.body\n'
p=lean/'PV_CB_Op223ForestProducerFuns.lean';assert not p.exists();p.write_text(s)
receipt=dict(raw_sha256={k:hashlib.sha256(v.encode()).hexdigest() for k,v in raw.items()},types_exact_blocks_after_namespace_rename_and_independent_declaration_reorder=True,external_exact_after_namespace_rename=True,shared_primitive_blocks=removed,adapted_sha256=hashlib.sha256(s.encode()).hexdigest(),change='Verified independent TraceCell/Bank declaration reordering only; namespace/import normalization and reuse of four byte-identical already compiled primitive declarations; generated forest function bodies unchanged. Same explicit universally quantified Range.contains parameter as the legacy helper; no template axiom installed.')
(ev/'RESUME5-FOREST-NORMALIZATION.json').write_text(json.dumps(receipt,indent=2)+'\n')
for k,v in raw.items():(ev/('RESUME5-FOREST-RAW-'+k+'.lean.txt')).write_text(v)
print(json.dumps(receipt,indent=2))
