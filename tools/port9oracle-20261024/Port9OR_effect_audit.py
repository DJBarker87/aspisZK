"""Independent inverse-lift audit of physical native batch source control."""
from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parents[2];L=R/'docs/research/100bit-spend-path-20261013/lean';E=R/'evidence/port9oracle-20261024'
n=(L/'Port3_NativeBatchBody.lean').read_text();a=n.index('  := do\n',n.index('def verifier.candidate.batch_tree_loop.body'))+len('  := do\n');b=n.index('\n/--',a);native=n[a:b]
s=(L/'Port9OR_BatchStep.lean').read_text();a=s.index('  do\n',s.index('def body '))+len('  do\n');b=s.index('\ntheorem source',a);generated=s[a:b]
lifts=0
while 'liftResult (' in generated:
 a=generated.index('liftResult (');o=a+len('liftResult ');depth=1;i=o+1
 while depth:
  if generated[i]=='(':depth+=1
  elif generated[i]==')':depth-=1
  i+=1
 generated=generated[:a]+generated[o+1:i-1]+generated[i:];lifts+=1
assert lifts==32,lifts
assert generated.count('Port4B_LeafCode.code tree q')==1
assert generated.count('verify root idx val d s3')==1
generated=generated.replace('Port4B_LeafCode.code tree q','ops.op6 aspis_coredigestDigest32Inst hash tree q')
generated=generated.replace('verify root idx val d s3','ops.op10 aspis_coredigestDigest32Inst hash multiproof.Arity.Two root idx val d s3')
generated=generated.replace('Port3_NativeBatchBody.multiproof.','multiproof.').replace('Port3_NativeBatchBody.verifier.candidate.batch_tree.closure.','verifier.candidate.batch_tree.closure.')
generated=re.sub(r'\bpure\b','ok',generated)
normalize=lambda t:re.sub(r'\s+','',t)
assert normalize(generated)==normalize(native),'inverse-lift source mismatch'
leaf=generated.index('ops.op6 aspis_coredigestDigest32Inst hash tree q')
assert leaf<generated.index('ops.op8 idx i4 index')<generated.index('ops.op7 val i5 leaf')
assert generated.index('ops.op10 aspis_coredigestDigest32Inst')>generated.index('ops.op0')
result={'kind':'independent-native-effect-source-audit-v1','inverse_lift_exact_nonwhitespace_control':True,'pure_Result_lifts':lifts,'leaf_callbacks':1,'verifier_callbacks':1,'duplicate_digest_precedes_index_and_digest_comparison':True,'terminal_callback_follows_count_and_padding_guards':True,'hashes':{n:hashlib.sha256((L/n).read_bytes()).hexdigest() for n in ['Port3_NativeBatchBody.lean','Port9OR_BatchStep.lean','Port4B_LeafCode.lean','Port9OR_P6Node.lean','Port9OR_P6Verify.lean','MultiproofConeRef/Funs.lean']},'boundary':'Source effect schedule audit, not an ELF/extraction identity gate or canonical model comparison.'}
(E/'effect-source-audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='hashes'}))
