#!/usr/bin/env python3
from pathlib import Path
import re,json,hashlib,sys
from generated_syntax import clean
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021/s6-forest-parent';S=B/'lean-candidates/s126-caller-boundary-20261021';G=E/'extraction/generated/AspisS6ForestParent'
new=clean((G/'Types.lean').read_text());old=(S/'S6FiveCodecTypesV1.lean').read_text();verified=[]
for match in re.finditer(r'(?m)^(def|structure|inductive)\s+([^\s(:]+)',new):
 kind,name=match[1],match[2]
 pat=r'(?m)^'+kind+r'\s+'+re.escape(name)+r'[\s\S]*?(?=\n(?:@\[|def\s|structure\s|inductive\s|end\s))'
 a=re.search(pat,new);b=re.search(pat,old);assert a and b,name
 assert re.sub(r'\s+','',a[0])==re.sub(r'\s+','',b[0]),name
 verified.append(name)
ports={'aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1':'AspisS6LateParent.encode','aspis_statement.pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1':'AspisS6SourceCodec.aspis_statement.pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1','aspis_statement.pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1':'AspisS6SourceCodec.aspis_statement.pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1','aspis_statement.atomic_statement.encode_digest_canonical':'AspisS6SourceCodec.aspis_statement.atomic_statement.encode_digest_canonical'}
ext=clean((G/'FunsExternal_Template.lean').read_text());assert ext.count('axiom ')==4
f=clean((G/'Funs.lean').read_text());f=f.replace('namespace AspisS6ForestParent','namespace AspisS6ForestParent\nopen AspisS6FiveUnrolledCodec',1)
for name,replacement in ports.items():
 assert name in ext
 f=re.sub(r'(?<![\w.])'+re.escape(name)+r'(?![\w.])',replacement,f)
# A formatter-only line-wrap collision in the monadic offset constant.
needle=r'(def aspis_statement.pool_v1.pair_forest_terminal.PAYMENT_STATEMENT_OFFSET[^\n]*? := do) (let [^\n]+)\n[ \t]+([^\n]+)'
before=f
f,count=re.subn(needle,lambda m:m[1]+'\n  '+m[2]+'\n  '+m[3],f)
assert count==1 and re.sub(r'\s+','',before)==re.sub(r'\s+','',f)
f='import S6LateParentSourceV1\nimport S6FullSourceCodecV1\nset_option autoImplicit false\n'+f
f+='\n#print axioms AspisS6ForestParent.encode\n'
assert not re.search(r'\b(Ops|axiom|opaque|sorry|native_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)',f)
p=S/'S6ForestParentSourceV1.lean'
if '--check' in sys.argv:assert p.read_text()==f
else:p.write_text(f)
m=dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(f.encode()).hexdigest(),raw_files={n:hashlib.sha256((G/n).read_bytes()).hexdigest() for n in ['Types.lean','Funs.lean','FunsExternal_Template.lean']},exact_native_type_owner='S6FiveCodecTypesV1',verified_full_types=verified,installed_source_children=ports,qualification='Unchanged frozen full forest validator and encoder source; complete native types and errors reused exactly. Four concrete source children installed, no arbitrary child operations. Prior reference transformations still require enclosing contextual/runtime/source/adoption and artifact re-pin gates.')
q=E/'materialization.json'
if '--check' in sys.argv:assert json.loads(q.read_text())==m
else:q.write_text(json.dumps(m,indent=2)+'\n')
