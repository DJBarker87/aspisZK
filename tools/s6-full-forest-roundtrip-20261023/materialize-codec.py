#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,sys
from generated_syntax import clean
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s126-current-caller-20261021/s6-full-forest-codec-extraction'
G=E/'source/renamed-generated/AspisS6FullForestCodec'
S=B/'lean-candidates/s126-caller-boundary-20261021'
def emit(p,s):
 if '--check' in sys.argv:assert p.read_text()==s,str(p)
 else:p.write_text(s)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
types='import Aeneas\nset_option autoImplicit false\n'+clean((G/'Types.lean').read_text())
types+='\n#print axioms AspisS6FullForestCodec.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1\n'
emit(S/'S6FullForestCodecTypesV1.lean',types)
base='aspis_statement.'
ports={base+'atomic_statement.encode_digest_canonical':'encDigest',base+'atomic_statement.decode_digest_canonical':'decDigest',base+'pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1':'validate',base+'pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1':'encWithdrawal',base+'pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1':'encTransfer',base+'pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1':'encLate',base+'pool_v1.pair_tree_profile.decode_pool_v1_pair_late_public_statement_boxed_v1':'decLate',base+'pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1':'decTransfer',base+'pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1':'decWithdrawal'}
external=clean((G/'FunsExternal_Template.lean').read_text());fields=[]
for m in re.finditer(r'(?m)^axiom\s+([^\s:]+)\s*:\s*([\s\S]*?)(?=\naxiom|\Z)',external):
 assert m[1] in ports,m[1]
 fields.append('  '+ports[m[1]]+' :\n'+ '\n'.join('    '+line.strip() for line in m[2].strip().splitlines()))
assert len(fields)==len(ports)==9
f=clean((G/'Funs.lean').read_text());matches=list(re.finditer(r'(?m)^def\s+([^\s(:]+)',f));blocks={}
for i,m in enumerate(matches):
 end=matches[i+1].start() if i+1<len(matches) else f.index('\nend AspisS6FullForestCodec',m.end())
 assert m[1] not in blocks
 body=f[m.end():end]
 for q,field in ports.items():body=re.sub(r'(?<![\w.])'+re.escape(q)+r'(?![\w.])','ops.'+field,body)
 blocks[m[1]]=(m.start(),end,body)
needed={n for n,(_,_,body) in blocks.items() if re.search(r'(?<![\w.])ops\.',body)}
while True:
 new=needed|{n for n,(_,_,body) in blocks.items() if any(re.search(r'(?<![\w.])'+re.escape(q)+r'(?![\w.])',body) for q in needed)}
 if new==needed:break
 needed=new
changes=[]
for n,(a,b,body) in blocks.items():
 if n not in needed:continue
 for q in sorted(needed,key=len,reverse=True):body=re.sub(r'(?<![\w.])'+re.escape(q)+r'(?![\w.])',q+' ops',body)
 changes.append((a,b,'def '+n+' (ops : Ops)'+body))
for a,b,new in sorted(changes,reverse=True):f=f[:a]+new+f[b:]
ns='namespace AspisS6FullForestCodec';assert f.count(ns)==1
f=f.replace(ns,ns+'\nstructure Ops where\n'+'\n'.join(fields)+'\n')
assert not any(re.search(r'(?<![\w.])'+re.escape(q)+r'(?![\w.])',f) for q in ports)
f='import S6FullForestCodecTypesV1\nset_option autoImplicit false\n'+f
for q in [base+'pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1',base+'pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1','encode','decode']:
 assert q in needed,q
 f+='\n#print axioms AspisS6FullForestCodec.'+q+'\n'
assert not re.search(r'\b(axiom|opaque|sorry|native_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)',f)
emit(S/'S6FullForestCodecNativeV1.lean',f)
emit(E/'materialization.json',json.dumps(dict(schema='focused-extractor-proof-packet-v1',raw={n:sha(G/n) for n in ['Types.lean','Funs.lean','FunsExternal_Template.lean']},candidates={n:sha(S/n) for n in ['S6FullForestCodecTypesV1.lean','S6FullForestCodecNativeV1.lean']},explicit_child_ports=ports,parameterized_definitions=sorted(needed),qualification='Complete actual native outer encoder and current boxed decoder, original full carriers and source control. Exactly nine nested child functions parameterized, no whole encoder/decoder replacement. Comments/metadata attributes/resource options removed, discriminants retained. No child correctness, allocator/runtime effect, native SDK or full codec roundtrip proof.'),indent=2)+'\n')
