#!/usr/bin/env python3
from pathlib import Path
import re,json,hashlib,sys
from generated_syntax import clean
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021/s6-snapshot-helper';S=B/'lean-candidates/s126-caller-boundary-20261021';G=E/'extraction/generated/AspisS6SnapshotHelper'
new=clean((G/'Types.lean').read_text());old=(S/'S6FiveCodecTypesV1.lean').read_text();name='aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1'
pat=r'(?m)^structure '+re.escape(name)+r'[\s\S]*?(?=\n(?:def|structure|inductive|end)\b)'
a=re.search(pat,new);b=re.search(pat,old);assert a and b
assert re.sub(r'\s+','',a[0])==re.sub(r'\s+','',b[0]),'Full native record fields/types must be unchanged'
external=clean((G/'FunsExternal_Template.lean').read_text());assert external.count('axiom ')==1
leaf='aspis_statement.atomic_statement.encode_digest_canonical';assert leaf in external
f=clean((G/'Funs.lean').read_text());f=f.replace('namespace AspisS6SnapshotHelper','namespace AspisS6SnapshotHelper\nopen AspisS6FiveUnrolledCodec',1)
f=re.sub(r'(?<![\w.])'+re.escape(leaf)+r'(?![\w.])','AspisS6SourceCodec.'+leaf,f)
f='import S6FullSourceCodecV1\nset_option autoImplicit false\n'+f
f+='\n#print axioms AspisS6SnapshotHelper.frontier_step\n#print axioms AspisS6SnapshotHelper.frontier_loop\n'
assert not re.search(r'\b(axiom|opaque|sorry|native_decide|Ops)\b|set_option\s+(maxHeartbeats|maxRecDepth)',f)
p=S/'S6SnapshotHelperSourceV1.lean'
if '--check' in sys.argv:assert p.read_text()==f
else:p.write_text(f)
m=dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(f.encode()).hexdigest(),raw_files={n:hashlib.sha256((G/n).read_bytes()).hexdigest() for n in ['Types.lean','Funs.lean','FunsExternal_Template.lean']},full_native_snapshot_type_owner='S6FiveCodecTypesV1',exact_full_native_fields_verified=True,installed_leaf='AspisS6SourceCodec.'+leaf,qualification='Complete extracted helper/loop with the original full native carrier and actual mutable Slice carrier on800-byte caller frames. Exactly one leaf installed from the checked complete source evaluator; no free operations. Native original/reference check precedes extraction. No enclosing codec/SDK or artifact closure.')
q=E/'materialization.json'
if '--check' in sys.argv:assert json.loads(q.read_text())==m
else:q.write_text(json.dumps(m,indent=2)+'\n')
