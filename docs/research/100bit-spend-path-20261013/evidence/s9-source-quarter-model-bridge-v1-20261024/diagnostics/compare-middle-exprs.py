from pathlib import Path
import re,json
root=Path('/tmp/a3-s9-source-quarter-model-bridge-v4-target-expr-check-20261023');s=(root/'evidence/lean.log').read_text();texts={}
for n in ['hs','hi','hf','hg']:
 t=s.split('QTYPE|'+n+'|',1)[1];t=t.split('\nQTYPE|',1)[0].split('\nQTARGET ',1)[0].split('\n/private/tmp/',1)[0];texts[n]=t

def parse(t):
 st=[];r=[];cur=r
 for tok in re.findall(r'\(|\)|[^\s()]+',t):
  if tok=='(':n=[];cur.append(n);st.append(cur);cur=n
  elif tok==')':cur=st.pop()
  else:cur.append(tok)
 return r

def tag(e,n):return isinstance(e,list) and e and e[0]=='Lean.Expr.'+n

def lift(e,k,d=0):
 if not isinstance(e,list):return e
 if tag(e,'bvar'):return [e[0],str(int(e[1])+k if int(e[1])>=d else int(e[1]))]
 if tag(e,'lam') or tag(e,'forallE'):return [e[0],e[1],lift(e[2],k,d),lift(e[3],k,d+1),e[4]]
 return [lift(x,k,d) for x in e]

def subst(e,a,d=0):
 if not isinstance(e,list):return e
 if tag(e,'bvar'):
  i=int(e[1]);return lift(a,d) if i==d else [e[0],str(i-1 if i>d else i)]
 if tag(e,'lam') or tag(e,'forallE'):return [e[0],e[1],subst(e[2],a,d),subst(e[3],a,d+1),e[4]]
 return [subst(x,a,d) for x in e]

def beta(e):
 if not isinstance(e,list):return e
 if tag(e,'mdata'):return beta(e[-1])
 e=[beta(x) for x in e]
 if tag(e,'app') and tag(e[1],'lam'):return beta(subst(e[1][3],e[2]))
 return e

def spine(e):
 args=[]
 while tag(e,'app'):args.append(e[2]);e=e[1]
 return e,list(reversed(args))
texts['target']=s.split('QTARGET ',1)[1].split('\n/private/tmp/',1)[0]
expr={n:beta(parse(t)) for n,t in texts.items()};eq={}
for n,e in expr.items():
 fn,ar=spine(e);assert tag(fn,'const') and fn[1]=='`Eq' and len(ar)==3;eq[n]=(ar[1],ar[2])
canon={'`'+n for n in re.findall(r'Lean.Expr.const\s+`([^\s]+\.E)\s',s)}
def norm(x):return '`AspisWideTower.WideExact' if x in canon else x

def diff(x,y,p='root'):
 if isinstance(x,str) or isinstance(y,str):return None if isinstance(x,str) and isinstance(y,str) and norm(x)==norm(y) else (p,x,y)
 if len(x)!=len(y):return (p+'.length',x,y)
 start=2 if x and y and x[0]==y[0] and x[0] in ['Lean.Expr.lam','Lean.Expr.forallE'] else 0
 for i in range(start,len(x)):
  d=diff(x[i],y[i],p+'.'+str(i))
  if d:return d
 return None
out={'canonicalized_type_aliases':sorted(canon),'beta_reduction_only':True,'comparisons':{}}
for a,b in [('hs','hi'),('hi','hf'),('hf','hg')]:
 d=diff(eq[a][1],eq[b][0]);out['comparisons'][a+'RHS-'+b+'LHS']=d
 print(a,b, str(d)[:2500])
out['endpoint_comparisons']={'targetLHS-hsLHS':diff(eq['target'][0],eq['hs'][0]),'hgRHS-targetRHS':diff(eq['hg'][1],eq['target'][1])}
print('ENDPOINTS',str(out['endpoint_comparisons'])[:5000])
(root/'middle-first-diffs.json').write_text(json.dumps(out,indent=2)+'\n')
