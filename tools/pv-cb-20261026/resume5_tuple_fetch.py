"""Retain actual tuple_cells extraction; replace only its one opaque range selector
with a named quantified parameter. No template axiom is installed. The producer
invariant must be proved uniformly over every selector, not for a chosen result.
"""
from pathlib import Path
import subprocess,json,hashlib
root=Path(__file__).resolve().parents[2]
ev=root/'evidence/pv-cb-20261026'
lean=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'
base='/home/dombarker/project-offloads/codex-pv-cb-20261026'
raw={}
for part in ['Types','Funs','FunsExternal_Template']:
 s=subprocess.check_output(['ssh','dombarker@100.108.41.90','cat',base+'/shipped-op223Tuple-generated/'+part+'.lean'],text=True)
 raw[part]=s
 (ev/'aeneas-source-op223Tuple-resume5-producer-r02'/(part+'.lean.txt')).write_text(s)
assert raw['FunsExternal_Template'].count('\naxiom ')==1
assert 'axiom core.ops.range.Range.contains' in raw['FunsExternal_Template']
assert 'aspis_statement.logup.compress_tagged_tuple' not in raw['FunsExternal_Template']
names={p:'PV_CB_Op223TupleProducer'+p for p in ['Types','External','Funs']}
for n in names.values():assert not (lean/(n+'.lean')).exists()
(lean/(names['Types']+'.lean')).write_text(raw['Types'])
external='''import Aeneas
import R1Z.PV_CB_Op223TupleProducerTypes
set_option autoImplicit false
namespace PV_CB_ShippedOp223Tuple
open Aeneas Aeneas.Std Result
/-- Unconstrained range-selector callback. Source postconditions are quantified
    over every instance, including failure/divergence. No source-output law is
    assumed, and no generated external axiom is installed. -/
class ExternalFuns where
  contains : {Idx U : Type} → core.cmp.PartialOrd Idx Idx →
    core.cmp.PartialOrd Idx U → core.cmp.PartialOrd U Idx →
    core.ops.range.Range Idx → U → Result Bool
abbrev core.ops.range.Range.contains [ops : ExternalFuns] := @ExternalFuns.contains ops
end PV_CB_ShippedOp223Tuple
'''
(lean/(names['External']+'.lean')).write_text(external)
s=raw['Funs'].replace('import PVCBShippedOp223Tuple.Types','import R1Z.'+names['Types']).replace('import PVCBShippedOp223Tuple.FunsExternal','import R1Z.'+names['External'])
s=s.replace('namespace PV_CB_ShippedOp223Tuple','namespace PV_CB_ShippedOp223Tuple\nvariable [ExternalFuns]',1)
s+='\n#print axioms PV_CB_ShippedOp223Tuple.pool_v1.pair_trace.tuple_cells\n#print axioms PV_CB_ShippedOp223Tuple.pool_v1.pair_trace.tuple_cells_loop\n#print axioms PV_CB_ShippedOp223Tuple.pool_v1.pair_trace.tuple_cells_loop.body\n'
(lean/(names['Funs']+'.lean')).write_text(s)
receipt=dict(raw_sha256={k:hashlib.sha256(v.encode()).hexdigest() for k,v in raw.items()},adapted={names[k]:hashlib.sha256((lean/(names[k]+'.lean')).read_bytes()).hexdigest() for k in names},change='Types unchanged. Funs imports renamed; named ExternalFuns parameter inserted, plus axioms audit commands. The only opaque function Range.contains becomes a named quantified class field with its exact type. Generated template retained only as inert text; no axiom/sorry is installed. All emitted source bodies and generated limits unchanged.',scope='A source-helper postcondition about tuple offsets can be proved uniformly over every range selector. This does not bind the actual compressor, prove registry refinement, or discharge an endpoint premise.')
(ev/'RESUME5-TUPLE-NORMALIZATION.json').write_text(json.dumps(receipt,indent=2)+'\n')
# Bind the actual producer and constant source, without altering the corpus.
inputs={}
for path in ['crates/aspis-statement/src/pool_v1/pair_trace.rs','crates/aspis-statement/src/poseidon2.rs']:
 b=subprocess.check_output(['ssh','dombarker@100.108.41.90','cat',base+'/source/'+path]);assert b==(root/path).read_bytes();inputs[path]=hashlib.sha256(b).hexdigest()
(ev/'RESUME5-PRODUCER-SOURCE-BINDING.json').write_text(json.dumps(inputs,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
