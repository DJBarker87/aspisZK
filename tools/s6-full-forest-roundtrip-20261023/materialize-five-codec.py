#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,sys
from generated_syntax import clean as clean_base
def clean(s):
 out=clean_base(s)
 # The transparent native field carrier needs reducibility for scalar instances.
 out=out.replace('def aspis_core.field.M31 :=','@[reducible]\ndef aspis_core.field.M31 :=')
 return out
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s126-current-caller-20261021/s6-five-codec-extraction'
G=E/'source/renamed-generated/AspisS6FiveUnrolledCodec'
S=B/'lean-candidates/s126-caller-boundary-20261021'
W=E.parent/'s6-five-codec-indent/generated/AspisS6FiveUnrolledCodec'
assert re.sub(r'\s+','',clean((G/'Funs.lean').read_text()))==re.sub(r'\s+','',clean((W/'Funs.lean').read_text())), 'Formatter may change only whitespace'

def emit(p,s):
 if '--check' in sys.argv:assert p.read_text()==s,str(p)
 else:p.write_text(s)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
types='import Aeneas\nimport S6NamedDiscriminantV1\nset_option autoImplicit false\n'+clean((G/'Types.lean').read_text())
assert types.count('@[discriminant u8 [1,2]]')==1
types=types.replace('@[discriminant u8 [1,2]]','@[s6_u8_discriminant]')
types+='\n#print axioms AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1\n'
emit(S/'S6FiveCodecTypesV1.lean',types)
base='aspis_statement.'
ports={'Slice.Insts.CoreCmpPartialEqArray.eq':'sliceArrayEq','core.option.Option.ok_or':'optionOkOr','core.option.Option.Insts.CoreCmpPartialEqOption.eq':'optionEq'}
external=clean((G/'FunsExternal_Template.lean').read_text());fields=[]
for m in re.finditer(r'(?m)^axiom\s+([^\s:]+)\s*([\s\S]*?)(?=\naxiom|\Z)',external):
 assert m[1] in ports,m[1]
 fields.append('  '+ports[m[1]]+'\n'+ '\n'.join('    '+line.strip() for line in m[2].strip().splitlines()))
assert len(fields)==len(ports)==3
f=clean((W/'Funs.lean').read_text())
f=re.sub(r'(?m)^ +(def|impl_def) ',r'\1 ',f)
narrow=re.sub(r'(?m)^ +(def|impl_def) ',r'\1 ',clean((G/'Funs.lean').read_text()))
# Four emitted monadic globals have a first do element on the header line.
# Reuse their original narrow layout; source tokens are identical.
repairs=[]
for name in ['aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES','aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES','aspis_statement.pool_v1.pair_forest_terminal.PAYMENT_STATEMENT_OFFSET','aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING']:
 pat=r'(?m)^def\s+'+re.escape(name)+r'(?=\s)[\s\S]*?(?=\n(?:def|impl_def)\s|\nend AspisS6FiveUnrolledCodec)'
 a=re.search(pat,narrow);b=re.search(pat,f);assert a and b,name
 assert re.sub(r'\s+','',a[0])==re.sub(r'\s+','',b[0]),name
 f=f[:b.start()]+a[0]+f[b.end():];repairs.append(name)
original_f=f
matches=list(re.finditer(r'(?m)^(?:def|impl_def)\s+([^\s(:]+)',f));blocks={}
for i,m in enumerate(matches):
 end=matches[i+1].start() if i+1<len(matches) else f.index('\nend AspisS6FiveUnrolledCodec',m.end())
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
 changes.append((a,b,('impl_def ' if f[a:].startswith('impl_def ') else 'def ')+n+' (ops : Ops)'+body))
for a,b,new in sorted(changes,reverse=True):f=f[:a]+new+f[b:]
ns='namespace AspisS6FiveUnrolledCodec';assert f.count(ns)==1
f=f.replace(ns,ns+'\nstructure Ops where\n'+'\n'.join(fields)+'\n')
assert not any(re.search(r'(?<![\w.])'+re.escape(q)+r'(?![\w.])',f) for q in ports)
f='import S6FiveCodecTypesV1\nset_option autoImplicit false\n'+f
for q in [base+'pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1',base+'pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1','encode','decode']:
 assert q in blocks,q
 f+='\n#print axioms AspisS6FiveUnrolledCodec.'+q+'\n'
assert not re.search(r'\b(axiom|opaque|sorry|native_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)',f)
emit(S/'S6FiveCodecNativeV1.lean',f)
emit(E/'materialization.json',json.dumps(dict(schema='focused-extractor-proof-packet-v1',raw={n:sha(G/n) for n in ['Types.lean','FunsExternal_Template.lean']},wide_funs_sha256=sha(W/'Funs.lean'),candidates={n:sha(S/n) for n in ['S6FiveCodecTypesV1.lean','S6FiveCodecNativeV1.lean']},explicit_child_ports=ports,parameterized_definitions=sorted(needed),formatting_only_globals=repairs,qualification='Complete codec extraction reference with five checked loop replacements, full carriers and source control. Exactly three standard-library operations remain explicit; no codec/validator ports. Comments/metadata attributes/resource options removed, discriminant readers and values retained; the closed u8 1/2 instance uses a type-qualified name via the original Aeneas reader generator. Standard-library installation, contextual transport, allocator/runtime effects, native SDK and full codec roundtrip remain unproved.'),indent=2)+'\n')

# Materialize the complete evaluator with actual current std Option bodies.
# The third external template is not referenced by any emitted function.
assert not re.search(r'(?<![\w.])Slice\.Insts\.CoreCmpPartialEqArray\.eq(?![\w.])',original_f)
closed=original_f
installed={'core.option.Option.ok_or':'AspisS6StdOptionMethods.option_ok_or','core.option.Option.Insts.CoreCmpPartialEqOption.eq':'AspisS6StdOptionMethods.option_eq'}
for name,replacement in installed.items():
 assert re.search(r'(?<![\w.])'+re.escape(name)+r'(?![\w.])',closed)
 closed=re.sub(r'(?<![\w.])'+re.escape(name)+r'(?![\w.])',replacement,closed)
closed=closed.replace('namespace AspisS6FiveUnrolledCodec','namespace AspisS6SourceCodec\nopen AspisS6FiveUnrolledCodec',1).replace('end AspisS6FiveUnrolledCodec','end AspisS6SourceCodec')
closed='import S6FiveCodecTypesV1\nimport S6StdOptionSourceV1\nset_option autoImplicit false\n'+closed
for name in ['encode','decode','aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1','aspis_statement.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1']:
 closed+='\n#print axioms AspisS6SourceCodec.'+name+'\n'
assert not re.search(r'\b(Ops|axiom|opaque|sorry|native_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)',closed)
emit(S/'S6FullSourceCodecV1.lean',closed)
emit(E/'source-codec-materialization.json',json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(closed.encode()).hexdigest(),type_owner='S6FiveCodecTypesV1',installed_actual_std_methods=installed,unused_external_template='Slice.Insts.CoreCmpPartialEqArray.eq',unreachable_external_reference_count=0,formatting_only_globals=repairs,qualification='Complete emitted codec and validation bodies, actual extracted Option methods installed, original full types reused. Unused external template has no caller in the generated function bodies. No free child operations or substitute account/statement carriers. Five checked reference loop transformations and contextual transport, full roundtrip, allocation/runtime and actual SDK connections remain explicit.'),indent=2)+'\n')
