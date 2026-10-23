#!/usr/bin/env python3
from pathlib import Path
import re,json,hashlib,sys
from generated_syntax import clean
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021/s6-afterstate-loop-parent';S=B/'lean-candidates/s126-caller-boundary-20261021';G=E/'extraction/generated/AspisS6AfterstateLoopParent'
new=clean((G/'Types.lean').read_text());old=(S/'S6FiveCodecTypesV1.lean').read_text();verified=[]
for name,kind in [('aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1','structure'),('aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1','inductive')]:
 pat=r'(?m)^'+kind+' '+re.escape(name)+r'[\s\S]*?(?=\n(?:@\[|def\s|structure\s|inductive\s|end\s))'
 a=re.search(pat,new);b=re.search(pat,old);assert a and b,name
 assert re.sub(r'\s+','',a[0])==re.sub(r'\s+','',b[0]),name
 verified.append(name)
ports={'aspis_statement.atomic_statement.encode_digest_canonical':'AspisS6SourceCodec.aspis_statement.atomic_statement.encode_digest_canonical','aspis_statement.pool_v1.pair_terminal.validate_verified_afterstate':'AspisS6SourceCodec.aspis_statement.pool_v1.pair_terminal.validate_verified_afterstate'}
ext=clean((G/'FunsExternal_Template.lean').read_text());assert ext.count('axiom ')==2
f=clean((G/'Funs.lean').read_text());f=f.replace('namespace AspisS6AfterstateLoopParent','namespace AspisS6AfterstateLoopParent\nopen AspisS6FiveUnrolledCodec',1)
for name,replacement in ports.items():
 assert name in ext
 f=re.sub(r'(?<![\w.])'+re.escape(name)+r'(?![\w.])',replacement,f)
f='import S6FullSourceCodecV1\nset_option autoImplicit false\n'+f
f+='\n#print axioms AspisS6AfterstateLoopParent.encode\n'
assert not re.search(r'\b(Ops|axiom|opaque|sorry|native_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)',f)
p=S/'S6AfterstateLoopParentSourceV1.lean'
if '--check' in sys.argv:assert p.read_text()==f
else:p.write_text(f)
m=dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(f.encode()).hexdigest(),raw_files={n:hashlib.sha256((G/n).read_bytes()).hexdigest() for n in ['Types.lean','Funs.lean','FunsExternal_Template.lean']},exact_native_type_owner='S6FiveCodecTypesV1',verified_full_types=verified,installed_source_children=ports,qualification='Actual enclosing afterstate encoder control/header/error source with its checked owned frontier loop. Full native carrier and error variants reused exactly; both leaves concretely installed, no arbitrary operations or success premises. Contextual/frozen-source/runtime/adoption and artifact re-pin gates remain explicit.')
q=E/'materialization.json'
if '--check' in sys.argv:assert json.loads(q.read_text())==m
else:q.write_text(json.dumps(m,indent=2)+'\n')
