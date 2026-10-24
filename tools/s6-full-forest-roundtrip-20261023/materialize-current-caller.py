#!/usr/bin/env python3
"""Pinned full current caller reuse and exact thin-decoder source cut."""
from pathlib import Path
import subprocess,hashlib,json,re,sys,runpy
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';S=B/'lean-candidates/s126-caller-boundary-20261021';E=B/'evidence/s126-current-caller-20261021'
revision='b797d6d360b460b527c046e37dad1106e8beeabc';sha=lambda s:hashlib.sha256(s.encode()).hexdigest();rows={}
def frozen(path,rev=revision):return subprocess.check_output(['git','show',rev+':'+str(path)],cwd=R,text=True)
def emit(path,content):
 if '--check' in sys.argv:assert path.read_text()==content,str(path)
 else:path.write_text(content)
for original,target in [('ImportUnionNamedDiscriminant','S6CurrentNamedDiscriminantV1'),('AdapterRwTypes','AdapterRwTypes'),('AdapterRwModel','AdapterRwModel'),('AdapterRwCuts','AdapterRwCuts')]:
 path=B.relative_to(R)/'lean'/(original+'.lean');raw=frozen(path);out=raw
 if original=='ImportUnionNamedDiscriminant':
  out=out.replace('ImportUnionNamedDiscriminant','AspisS6CurrentNamedDiscriminant').replace('import_union_discriminant','s6_current_discriminant').replace('namedDiscriminant','s6CurrentDiscriminant')
  out+='\n#print axioms AspisS6CurrentNamedDiscriminant.s6CurrentDiscriminantAttribute\n'
  transform='Namespace, syntax/attribute spelling and GLOBAL builtin attribute key renamed to coexist with historical prototype. Original Aeneas reader/instance generator bodies, enum types, tags and qualified generated instance names retained.'
 elif original=='AdapterRwTypes':
  out=out.replace('import ImportUnionNamedDiscriminant','import S6CurrentNamedDiscriminantV1').replace('import_union_discriminant','s6_current_discriminant')
  out+='\n#print axioms AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1\n'
  transform='Naming-adapter import and attribute spelling only; all complete carriers and original module/namespace retained; append axioms audit.'
 elif original=='AdapterRwModel':
  out+='\n#print axioms AdapterRw.Ops\n';transform='Append Ops axioms audit only; complete original module, namespace and source bodies retained.'
 else:transform='Verbatim original source, module and namespace; no edits.'
 emit(S/(target+'.lean'),out);rows[target]=dict(original=str(path),revision=revision,original_sha256=sha(raw),candidate_sha256=sha(out),transform=transform)
emit(E/'s6-current-adapter-materialization.json',json.dumps(dict(schema='focused-extractor-proof-packet-v1',sources=rows),indent=2)+'\n')
p=S/'S2OwnedStage1ModelV1.lean';raw=p.read_text();start=raw.index('def decode_public_statement_box.closure.Insts.');end=raw.index('/-- [aspis_s126_owned_stage1::(owned_stage1_tail',start)
body=re.sub(r'/\-[\s\S]*?\-/','',raw[start:end]).replace('ops.op5','ops.decode')
out='''import AdapterRwModel
set_option autoImplicit false
open Aeneas Aeneas.Std Result AdapterRw
namespace AspisS6CurrentBoxedDecoderSource

/-- The sole original child of the extracted thin boxed decoder. -/
structure Ops where
  decode : Slice U8 → Result (core.result.Result
    AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
    AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)

def decode_public_statement_box.closure := Unit

'''+body+'''\n#print axioms decode_public_statement_box
end AspisS6CurrentBoxedDecoderSource
'''
emit(S/'S6CurrentBoxedDecoderSourceV1.lean',out)
meta=dict(schema='focused-extractor-proof-packet-v1',original=str(p.relative_to(R)),original_sha256=sha(raw),source_span_sha256=sha(raw[start:end]),candidate_sha256=sha(out),transform='Exact three original extracted thin-decoder declarations; comments stripped, namespace relocated, full AdapterRw nominal carriers selected, sole called Ops field op5 renamed decode. Full checked carrier bijections. Box/ownership erasure is inherited extraction TCB, not a native allocation/effect theorem.')
emit(E/'s6-current-boxed-decoder-materialization.json',json.dumps(meta,indent=2)+'\n')
functions=runpy.run_path(str(R/'tools/s6-full-forest-roundtrip-20261023/check-native-parent-source-pins.py'))['functions']
file='programs/r1-cost-probe/src/r1_pool_adapter.rs';revisions=['b2727acd3abf79315d18b754a260f58f4b1c6326','25866ec331cc7ce27dd9956609c11d32fa8fa58a',revision]
texts={rev:frozen(file,rev) for rev in revisions}
captured=E/'modular-host/sources/owned-tail-v1/src/lib.rs';texts[str(captured.relative_to(R))]=captured.read_text()
spans={name:functions(text,'decode_public_statement_box') for name,text in texts.items()};assert all(len(v)==1 for v in spans.values())
assert len({sha(v[0]) for v in spans.values()})==1
meta=dict(schema='focused-extractor-proof-packet-v1',source_file=file,whole_file_sha256={k:sha(v) for k,v in texts.items()},byte_equal_boxed_decoder_span={k:sha(v[0]) for k,v in spans.items()},qualification='Original thin Rust Box::new/error-map wrapper span equals current research and frozen/retained extraction reference. Other adapter contents differ. No state, allocation, native accepted-event or abort-trace transport inferred.')
verifier='crates/aspis-r1-cost-probe/src/verifier.rs'
verifier_hashes={rev:sha(frozen(verifier,rev)) for rev in revisions};assert len(set(verifier_hashes.values()))==1
meta['whole_verifier_file_equal']=dict(file=verifier,sha256=verifier_hashes)
program='programs/r1-cost-probe/src/lib.rs';program_texts={rev:frozen(program,rev) for rev in revisions};program_texts[str(captured.relative_to(R))]=captured.read_text()
first_spans={k:functions(text,'first_decoded') for k,text in program_texts.items()};assert all(len(v)==1 for v in first_spans.values());assert len({sha(v[0]) for v in first_spans.values()})==1
meta['first_decoded_spans_equal']=dict(file=program,sha256={k:sha(v[0]) for k,v in first_spans.items()})
emit(E/'s6-current-caller-source-pins.json',json.dumps(meta,indent=2)+'\n')
print(json.dumps(dict(current_modules=len(rows),boxed_source_cut=True,wrapper_spans_equal=len(spans))))
