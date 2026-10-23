#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s126-current-caller-20261021/s6-full-forest-encoder-extraction'
G=E/'included-encoder/source/generated/AspisS6FullForestEncoder'
S=B/'lean-candidates/s126-caller-boundary-20261021'
def emit(path,text):
 if '--check' in sys.argv:assert path.read_text()==text,str(path)
 else:path.write_text(text)
def clean(s):
 s=re.sub(r'/\*[\s\S]*?\*/','',s)
 s=re.sub(r'/-[\s\S]*?-/', '',s)
 s=re.sub(r'(?m)^--[^\n]*\n','',s)
 # Attribute payloads may contain nested discriminant value lists.
 def attrs(text):
  out='';i=0
  while True:
   a=text.find('@[',i)
   if a<0:return out+text[i:]
   out+=text[i:a];j=a+2;depth=1
   while depth:
    depth+=(text[j]=='[')-(text[j]==']');j+=1
   block=text[a+2:j-1]
   disc=re.search(r'discriminant\s+\w+\s+\[[^]]*\]',block)
   if disc:out+='@['+disc[0]+']'
   i=j
 s=attrs(s)
 s=re.sub(r'(?m)^set_option[^\n]*\n','',s)
 s=re.sub(r'(?m)^import[^\n]*\n','',s)
 return s
# Keep the complete generated nominal carriers, no simplification.
types='import Aeneas\nset_option autoImplicit false\n'+clean((G/'Types.lean').read_text())
types+='\n#print axioms AspisS6FullForestEncoder.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1\n'
emit(S/'S6FullForestEncoderTypesV1.lean',types)
base='aspis_statement.'
ports={base+'atomic_statement.encode_digest_canonical':'digest',base+'pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1':'validate',base+'pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1':'withdrawal',base+'pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1':'transfer',base+'pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1':'late'}
ops='''
structure Ops where
 digest : Array aspis_core.field.M31 8#usize → Result (Array U8 32#usize)
 validate : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 →
   Result (core.result.Result Unit aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
 withdrawal : aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 →
   Result (core.result.Result (Array U8 216#usize) aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError)
 transfer : aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 →
   Result (core.result.Result (Array U8 216#usize) aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError)
 late : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 → Slice U8 →
   Result ((core.result.Result Unit aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) × Slice U8)
'''
f=clean((G/'Funs.lean').read_text());ns='namespace AspisS6FullForestEncoder'
assert f.count(ns)==1;f=f.replace(ns,ns+'\n'+ops)
main=base+'pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1'
# Only the main encoder and direct wrapper depend on these child functions.
matches=list(re.finditer(r'(?m)^def\s+([^\s(:]+)',f));changes=[]
for i,m in enumerate(matches):
 end=matches[i+1].start() if i+1<len(matches) else f.index('\nend AspisS6FullForestEncoder',m.end())
 name=m[1]
 if name not in [main,'encode']:continue
 body=f[m.end():end]
 for q,field in ports.items():body=re.sub(re.escape(q)+r'(?![\w.])','ops.'+field,body)
 body=re.sub(re.escape(main)+r'(?![\w.])',main+' ops',body)
 changes.append((m.start(),end,'def '+name+' (ops : Ops)'+body))
assert len(changes)==2
for a,b,new in reversed(changes):f=f[:a]+new+f[b:]
assert not any(re.search(re.escape(q)+r'(?![\w.])',f) for q in ports)
f='import S6FullForestEncoderTypesV1\nset_option autoImplicit false\n'+f
f+='\n#print axioms AspisS6FullForestEncoder.'+main+'\n#print axioms AspisS6FullForestEncoder.encode\n'
assert not re.search(r'\b(axiom|opaque|sorry|native_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)',f)
emit(S/'S6FullForestEncoderNativeV1.lean',f)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
emit(E/'materialization.json',json.dumps(dict(schema='focused-extractor-proof-packet-v1',raw={n:sha(G/n) for n in ['Types.lean','Funs.lean','FunsExternal_Template.lean']},candidates={n:sha(S/n) for n in ['S6FullForestEncoderTypesV1.lean','S6FullForestEncoderNativeV1.lean']},transformations=['Remove generated comments, rust metadata attributes (retain discriminants), imports and resource/linter options','Retain all complete generated nominal carriers and source control/operations/constants','Replace exactly five external child functions by explicit Ops fields; parameterize main encoder and direct wrapper only'],qualification='Exact actual native outer source with explicit nested child ports. No whole opaque replacement or imported axiom templates. No child success/roundtrip/frame contracts, SDK/runtime allocation model or whole codec closure proved.'),indent=2)+'\n')
