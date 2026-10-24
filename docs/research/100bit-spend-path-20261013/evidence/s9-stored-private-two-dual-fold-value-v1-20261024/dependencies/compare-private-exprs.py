from pathlib import Path
import re,json,collections
s=Path('/tmp/a3-compare-quarter-exprs-v2.py').read_text();ns={'re':re};exec(s[s.index('def parse'):s.index("texts['target']")],ns);parse,beta,spine,tag=[ns[k]for k in ['parse','beta','spine','tag']]
s=Path('/tmp/factor-private-v3-expr.log').read_text();v=s.split('PRIVATE-VALUE-EXPR ',1)[1].split('PRIVATE-MATH-EXPR ',1)[0];m=s.split('PRIVATE-MATH-EXPR ',1)[1].split('\n/home/dombarker',1)[0];a=spine(beta(parse(v)))[1][2];b=spine(beta(parse(m)))[1][2];names=set(re.findall(r'Lean.Expr.const\s+`([^\s]+\.E)\s',s));
def norm(x):
 if isinstance(x,str):return '`AspisWideTower.WideExact'if x.lstrip('`')in names else x
 if tag(x,'lam')or tag(x,'forallE'):return[x[0],'BINDER',norm(x[2]),norm(x[3]),x[4]]
 return[norm(y)for y in x]
a=norm(a);b=norm(b);ds=[]
def diff(x,y,p='root'):
 if x==y:return
 if isinstance(x,str)or isinstance(y,str)or len(x)!=len(y):ds.append((p,x,y));return
 for i,(xx,yy)in enumerate(zip(x,y)):diff(xx,yy,p+'.'+str(i))
diff(a,b);Path('/tmp/factor-private-expression-differences.json').write_text(json.dumps(ds,indent=2));print('diffs',len(ds));print(str(ds)[:13000]);print('aliases',names)
