"""Cut long parser continuations into bounded symbolic source proofs."""
from pathlib import Path
import ast,json,re,subprocess,hashlib
R=Path(__file__).resolve().parents[2];D=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-rjdec-20261028';plan=json.loads((E/'build-plan.json').read_text())
old=subprocess.check_output(['git','show','HEAD:tools/pv-world-20261028/reify-recursive.py'],text=True);ns=dict(re=re,json=json);exec(compile(ast.Module(body=[n for n in ast.parse(old).body if isinstance(n,(ast.FunctionDef,ast.ClassDef))],type_ignores=[]),'world-translator','exec'),ns)
local={'ns':ns};exec(compile(ast.Module(body=[n for n in ast.parse((R/'tools/pv-rjdec-20261028/reify-decoders.py').read_text()).body if isinstance(n,ast.FunctionDef)],type_ignores=[]),'layout','exec'),local);ns['normalize']=local['normalize_columns'];rawemit=ns['emit'];rawproof=ns['proof'];mapping={};order=[]
def emit(node,n=2,calls=None):
 if node.kind=='call':
  expr=node.expr;label=expr.split()[0]
  if label in mapping:
   return ns['spaces'](mapping[label]+'.program '+expr[len(label):].strip(),n)
 return rawemit(node,n,calls)
def proof(node,n=2):
 if node.kind=='call':
  expr=node.expr;label=expr.split()[0]
  if label in mapping:return ns['spaces']('exact '+mapping[label]+'.source ops '+expr[len(label):].strip(),n)
 return rawproof(node,n)
ns['emit']=emit;ns['proof']=proof
mapping['atomic_statement.decode_digest_canonical']='R1Z.PV_RJDec_Parser03';mapping['pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1']='R1Z.PV_RJDec_Parser14';mapping['pool_v1.pair_terminal.validate_verified_afterstate']='R1Z.PV_RJDec_Parser05'
def make(mod,src,fun,header,result,body,args,extra_imports=(),top=None,reference=False):
 node=ns['parse'](ns['normalize'](body));calls=[]
 imports=[src,'R1Z.PV_W_IfLaws']+list(mapping.values())+list(extra_imports)
 imports=list(dict.fromkeys(imports));text=''.join('import '+i+'\n' for i in imports)+'set_option autoImplicit false\nnoncomputable section\nnamespace '+mod+'\nopen Aeneas Aeneas.Std AspisR1TerminalDecoder PV_W_TypedEffects PV_W_RecursiveLaws\nopen pool_v1.pair_tree_profile pool_v1.pair_terminal\nvariable [ProverRwFull.ExternalTypes]\n\n'
 if reference:
  text+='open Aeneas.Std.Result\n\n'
  text+='def reference '+header+' : Result '+result+' := do\n'+body+'\n\n'
  fun=mod+'.reference'
 text+='def program '+header+' : P '+result+' := do\n'+emit(node,calls=calls).replace('letI : ExternalFuns := ops','letI : ProverRwFull.ExternalFuns := ops')+'\n\n'
 targetfun=fun
 text+='theorem '+('source_chunk' if top else 'source')+' (ops : ProverRwFull.ExternalFuns) '+header+' :\n  erase ops (program '+' '.join(args)+') = '+fun+' '+' '.join(args)+' := by\n  unfold program '+fun+'\n'+proof(node)+'\n\n'
 if top:
  if reference:
   text+='theorem reference_source '+header+' : reference '+' '.join(args)+' = '+top+' '+' '.join(args)+' := by\n  pv_kernel_refl\n\n'
   link='reference_source '+' '.join(args)
  else:link='PV_RunJoin_DecoderPrefix29.source '+' '.join(args)
  text+='theorem source (ops : ProverRwFull.ExternalFuns) '+header+' :\n  erase ops (program '+' '.join(args)+') = '+top+' '+' '.join(args)+' :=\n  (source_chunk ops '+' '.join(args)+').trans ('+link+')\n\n'
 text+='#print axioms source\n'+('#print axioms source_chunk\n' if top else '')+('#print axioms reference_source\n' if top and reference else '')+'end '+mod+'\n'
 (D/(mod.split('.')[-1]+'.lean')).write_text(text);order.append(mod)
 return targetfun
# Reuse the already checked symbolic continuation boundaries for snapshot.
for n in [20,16,12,8,4,0]:
 short='PV_RunJoin_DecoderStage'+str(n)+'29';p=D/(short+'.lean');ns['s']=p.read_text();header,result,body,args,_=ns['get']('run');mod='R1Z.PV_RJDec_SnapshotChunk'+str(n).zfill(2)
 make(mod,'R1Z.'+short,'R1Z.'+short+'.run',header,result,body,args);mapping[short+'.run']=mod
p=D/'PV_RunJoin_DecoderPrefix29.lean';ns['s']=p.read_text();header,result,body,args,_=ns['get']('run');make('R1Z.PV_RJDec_ParserR12','R1Z.PV_RunJoin_DecoderPrefix29','R1Z.PV_RunJoin_DecoderPrefix29.run',header,result,body,args,top='pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1')
# The afterstate decoder alternates raw byte and canonical digest binds.
pin=plan['modules']['AspisR1TerminalDecoder.Funs'];ns['s']=subprocess.check_output(['git','show','HEAD:'+pin['path']],text=True);original='pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1';header,result,body,args,_=ns['get'](original);lines=body.splitlines();cuts=[9,17,25,33,41]
indent=ns['indent']
def arm(k):
 i=next(i for i,l in enumerate(lines) if re.search(r'\.Continue val'+str(k)+r' =>',l));base=indent(lines[i]);end=i+1
 while end<len(lines) and indent(lines[end])>base:end+=1
 return i+1,end

def flatten(xs):
 base=indent(xs[0]);return '\n'.join('  '+x[base:] for x in xs)
def cut_child(xs,nextk):
 i=next(i for i,l in enumerate(xs) if re.search(r'\.Continue val'+str(nextk)+r' =>',l));base=indent(xs[i]);end=i+1
 while end<len(xs) and indent(xs[end])>base:end+=1
 params='bytes '+' '.join('val'+str(j) for j in range(1,nextk+1,2));call='R1Z.PV_RJDec_AfterChunk'+str(nextk)+'.reference '+params
 return xs[:i+1]+[' '*(base+2)+call]+xs[end:]
for ix,k in reversed(list(enumerate(cuts))):
 start,end=arm(k);xs=lines[start:end]
 if ix+1<len(cuts):xs=cut_child(xs,cuts[ix+1])
 ps=['bytes']+['val'+str(j) for j in range(1,k+1,2)];h='(bytes : Slice U8) ('+' '.join(ps[1:])+' : Array U32 8#usize)';mod='R1Z.PV_RJDec_AfterChunk'+str(k)
 make(mod,'AspisR1TerminalDecoder.Funs','reference',h,result,flatten(xs),ps,reference=True);mapping[mod+'.reference']=mod
xs=cut_child(lines,cuts[0]);make('R1Z.PV_RJDec_ParserR15','AspisR1TerminalDecoder.Funs','reference',header,result,flatten(xs),args,extra_imports=['R1Z.PV_RunJoin_KernelRefl29'],top=original,reference=True)
(E/'chunked-parsers.json').write_text(json.dumps(dict(order=order,source_pin=pin,note='replacement for unchunked recursion-depth failure; original failure retained; source Result only'),indent=2)+'\n');print(order)
