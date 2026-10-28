"""Syntax translation of pinned extracted do trees, with finite erasure proofs.
No function is evaluated. Unsupported syntax is rejected rather than erased.
"""
from pathlib import Path
import re,json,hashlib,subprocess,sys
R=Path(__file__).resolve().parents[2];D=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-world-20261028'
source='docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean'
s=(R/source).read_text();assert s.encode()==subprocess.check_output(['git','show','HEAD:'+source])
# These translations are independent modules; recursive direct helper expansion
# is selected explicitly, preserving opaque leaves as obligations in the census.
CONFIG=[
 ('prover.prove_masked_with_attempt','MaskedWithAttempt'),
 ('aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1','ReserveBuild'),
 ('aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reservation_path','ReservationPath'),
 ('prover.derive_private_salts','PrivateSalts'),
 ('prover.prove_from_semantics','FromSemantics'),
]

def get(name):
 m=re.search(r'\ndef\s+'+re.escape(name)+r'\s*(?=\(|\{)',s);assert m,name
 begin=m.end();end=s.index('\n\n',begin);text=s[begin:end];h,b=text.split(':= do\n',1)
 assert 'partial_fixpoint' not in b,name
 # Extract header's argument names by balanced delimiters; return type starts ':'.
 h=h.strip();pos=0;args=[];explicit=[]
 while pos<len(h) and h[pos] in '({':
  start=pos;stack=[]
  while pos<len(h):
   c=h[pos]
   if c in '({[':stack.append(c)
   elif c in ')}]':stack.pop()
   pos+=1
   if not stack:break
  binder=h[start+1:pos-1];names=binder.split(':',1)[0].split();args+=names
  if h[start]=='(':explicit+=names
  while pos<len(h) and h[pos].isspace():pos+=1
 assert h[pos]==':',h[pos:]
 result=h[pos+1:].strip();assert result.startswith('Result '),result
 return h[:pos].strip(),result[7:].strip(),b,args,explicit

def indent(x):return len(x)-len(x.lstrip())
def normalize(body):
 lines=body.splitlines();out=[];i=0
 while i<len(lines):
  line=lines[i];i+=1
  if not line.strip():continue
  pad=' '*indent(line);t=line.strip()
  if t=='|':
   t+=' '+lines[i].strip();i+=1
  if t.startswith('| '):
   while '=>' not in t:t+=' '+lines[i].strip();i+=1
   pattern,rhs=t.split('=>',1);out.append(pad+pattern.strip()+' =>')
   if rhs.strip():out.append(pad+'  '+rhs.strip())
  elif t.startswith(('then ','else ')):
   word,rest=t.split(' ',1);out += [pad+word,pad+'  '+rest]
  else:out.append(line)
 return out

class Node:
 def __init__(self,kind,**kw):self.kind=kind;self.__dict__.update(kw)

def parse(lines,base=None):
 assert lines
 if base is None:base=indent(lines[0])
 assert indent(lines[0])==base,lines[:3]
 t=lines[0].strip()
 if t=='do':return parse(lines[1:])
 if t.startswith('let '):
  i=1
  while i<len(lines) and indent(lines[i])>base:i+=1
  chunk=lines[:i];rest=lines[i:];assert rest,chunk
  if '←' in t:
   pre,expr=t.split('←',1);exprlines=[(' '*(base+2)+expr.strip())] if expr.strip() else []
   exprlines+=chunk[1:]
   return Node('bind',var=pre[4:].strip(),expr=parse(exprlines),next=parse(rest,base))
  return Node('let',text='\n'.join(chunk),next=parse(rest,base))
 if t.startswith('if '):
  i=0;conds=[]
  while i<len(lines) and not lines[i].strip().endswith('then') and lines[i].strip()!='then':conds.append(lines[i].strip());i+=1
  if lines[i].strip()=='then':pass
  else:conds.append(lines[i].strip()[:-4].strip())
  cond=' '.join(conds)[3:].strip();assert cond
  i+=1;j=i
  while j<len(lines) and not (indent(lines[j])==base and lines[j].strip()=='else'):j+=1
  assert j<len(lines),(t,lines[-3:])
  return Node('if',cond=cond,yes=parse(lines[i:j]),no=parse(lines[j+1:]))
 if t.startswith('match '):
  assert t.endswith(' with'),t
  i=1;branches=[]
  while i<len(lines):
   assert indent(lines[i])==base and lines[i].strip().startswith('| '),lines[i]
   pattern=lines[i].strip()[2:-2].strip();j=i+1
   while j<len(lines) and indent(lines[j])>base:j+=1
   child=lines[i+1:j]
   if child and child[0].strip()=='do':child=child[1:]
   branches.append((pattern,parse(child)));i=j
  return Node('match',discr=t[6:-5].strip(),branches=branches)
 i=1
 while i<len(lines) and indent(lines[i])>base:i+=1
 if i<len(lines):return Node('bind',var='_',expr=parse(lines[:i]),next=parse(lines[i:],base))
 expr='\n'.join(x.strip() for x in lines)
 return Node('pure' if (t=='ok' or t.startswith('ok ')) else 'call',expr=expr[3:] if (t=='ok' or t.startswith('ok ')) else expr)

def spaces(text,n):return '\n'.join(' '*n+x for x in text.splitlines())

def emit(node,n=2,calls=None):
 pad=' '*n;k=node.kind
 if k=='let':return spaces('\n'.join(x.strip() for x in node.text.splitlines()),n)+'\n'+emit(node.next,n,calls)
 if k=='bind':
  exp=emit(node.expr,n+2,calls).lstrip()
  # do syntax needs an explicit nested do for structured bind expressions.
  structured=node.expr.kind not in ['call','pure']
  return pad+'let '+node.var+' ← '+('do\n'+spaces(exp,n+2) if structured else exp)+'\n'+emit(node.next,n,calls)
 if k=='if':return pad+'if '+node.cond+' then\n'+emit(node.yes,n+2,calls)+'\n'+pad+'else\n'+emit(node.no,n+2,calls)
 if k=='match':return pad+'match '+node.discr+' with\n'+'\n'.join(pad+'| '+p+' =>\n'+emit(c,n+2,calls) for p,c in node.branches)
 if k=='pure':return pad+'pure '+node.expr.replace('\n','\n'+pad+'  ')
 expr=node.expr;label=expr.split()[0];calls.append(dict(label=label,expression=expr))
 # Typed filesystem operations are handled by the existing typed reifier.
 return pad+'invoke '+json.dumps(label)+' (fun ops =>\n'+pad+'  letI : ExternalFuns := ops\n'+spaces(expr,n+2)+')'

def proof(node,n=2):
 pad=' '*n;k=node.kind
 if k=='let':return pad+'try dsimp only\n'+proof(node.next,n)
 if k=='bind':
  var=node.var
  intro=('rintro ⟨'+var[1:-1]+'⟩') if var.startswith('(') else 'intro '+var
  return pad+'try dsimp only\n'+pad+'rw [erase_bind]\n'+pad+'apply PV_W_RecursiveLaws.bind_congr\n'+pad+'·\n'+proof(node.expr,n+2)+'\n'+pad+'· '+intro+'\n'+proof(node.next,n+2)
 if k=='if':return pad+'try dsimp only\n'+pad+'apply PV_W_IfLaws.erase_if_congr\n'+pad+'·\n'+proof(node.yes,n+2)+'\n'+pad+'·\n'+proof(node.no,n+2)
 if k=='match':
  out=pad+'try dsimp only\n'+pad+'cases '+node.discr+' with\n'
  for ix,(p,c) in enumerate(node.branches):
   ps=p.split();ctor=ps[0].split('.')[-1];args=[('unused'+str(ix)+'_'+str(i)) if a=='_' else a for i,a in enumerate(ps[1:])]
   out+=pad+'| '+ctor+(' '+' '.join(args) if args else '')+' =>\n'+proof(c,n+2)+'\n'
  return out.rstrip()
 return pad+('rfl' if k=='pure' else 'exact erase_invoke ops _ _')

selected=sys.argv[1] if len(sys.argv)>1 else None
for name,short in CONFIG:
 if selected and short!=selected:continue
 header,result,body,args,explicit=get(name);node=parse(normalize(body));calls=[]
 out='import R1Z.PV_W_IfLaws\nset_option autoImplicit false\nnoncomputable section\nnamespace R1Z.PV_W_'+short+'\nopen Aeneas Aeneas.Std ProverRwFull PV_W_TypedEffects\nopen PV_W_RecursiveLaws\nvariable [ExternalTypes]\n\n'
 out+='def program\n  '+header+' :\n  P '+result+' := do\n'+emit(node,calls=calls)+'\n\n'
 # implicit T0 is passed explicitly to source to remove ambiguity.
 actual='@'+name+' _ ops '+ ' '.join(args)
 out+='theorem erase_program (ops : ExternalFuns)\n  '+header+' :\n  erase ops (program '+ ' '.join(explicit)+') =\n    '+actual+' := by\n  unfold program '+name+'\n'+proof(node)+'\n\n#print axioms erase_program\nend R1Z.PV_W_'+short+'\n'
 target=D/('PV_W_'+short+'.lean')
 if '--check' in sys.argv:assert target.read_text()==out
 else:target.write_text(out)
 (E/('d372-reify-'+short+'.json')).write_text(json.dumps(dict(source=source,source_sha256=hashlib.sha256(s.encode()).hexdigest(),body_sha256=hashlib.sha256(body.encode()).hexdigest(),name=name,module='R1Z.PV_W_'+short,calls=calls,scope='exact Lean-source reification; native helper/primitive effects remain obligations'),indent=2)+'\n')
 print(short,len(calls),'calls')
