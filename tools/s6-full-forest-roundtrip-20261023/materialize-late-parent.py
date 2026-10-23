#!/usr/bin/env python3
from pathlib import Path
import re,json,hashlib,sys
from generated_syntax import clean
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021/s6-late-parent';S=B/'lean-candidates/s126-caller-boundary-20261021';G=E/'extraction/generated/AspisS6LateParent'
new=clean((G/'Types.lean').read_text());old=(S/'S6FiveCodecTypesV1.lean').read_text();verified=[]
for match in re.finditer(r'(?m)^(def|structure|inductive)\s+([^\s(:]+)',new):
 kind,name=match[1],match[2]
 pat=r'(?m)^'+kind+r'\s+'+re.escape(name)+r'[\s\S]*?(?=\n(?:@\[|def\s|structure\s|inductive\s|end\s))'
 a=re.search(pat,new);b=re.search(pat,old);assert a and b,name
 assert re.sub(r'\s+','',a[0])==re.sub(r'\s+','',b[0]),name
 verified.append(name)
ports={'core.option.Option.Insts.CoreCmpPartialEqOption.eq':'AspisS6StdOptionMethods.option_eq','aspis_statement.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1':'AspisS6AfterstateLoopParent.encode','aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1':'AspisS6SnapshotLoopParent.encode'}
ext=clean((G/'FunsExternal_Template.lean').read_text());assert ext.count('axiom ')==3
f=clean((G/'Funs.lean').read_text());f=f.replace('namespace AspisS6LateParent','namespace AspisS6LateParent\nopen AspisS6FiveUnrolledCodec',1)
for name,replacement in ports.items():
 assert name in ext
 f=re.sub(r'(?<![\w.])'+re.escape(name)+r'(?![\w.])',replacement,f)
f='import S6SnapshotLoopParentSourceV1\nimport S6AfterstateLoopParentSourceV1\nimport S6StdOptionSourceV1\nset_option autoImplicit false\n'+f
f+='\n#print axioms AspisS6LateParent.encode\n'
assert not re.search(r'\b(Ops|axiom|opaque|sorry|native_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)',f)
p=S/'S6LateParentSourceV1.lean'
if '--check' in sys.argv:assert p.read_text()==f
else:p.write_text(f)
m=dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(f.encode()).hexdigest(),raw_files={n:hashlib.sha256((G/n).read_bytes()).hexdigest() for n in ['Types.lean','Funs.lean','FunsExternal_Template.lean']},exact_native_type_owner='S6FiveCodecTypesV1',verified_full_types=verified,installed_source_children=ports,qualification='Unchanged frozen enclosing lane-transition encoder source; complete native types and errors reused exactly. Both source encoder references and actual std Option method concretely installed, no arbitrary child operations. Five prior/refined loop transformations still require enclosing contextual/runtime/source/adoption and artifact re-pin gates.')
q=E/'materialization.json'
if '--check' in sys.argv:assert json.loads(q.read_text())==m
else:q.write_text(json.dumps(m,indent=2)+'\n')
