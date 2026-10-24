from pathlib import Path
import re,json
s=Path('/tmp/a3-compare-quarter-exprs-v2.py').read_text();a=s.index('def parse');b=s.index("texts['target']");ns={"re":re};exec(s[a:b],ns);parse=ns['parse'];beta=ns['beta'];tag=ns['tag']
a=beta(parse(Path('/tmp/factor-low-shape-expr.txt').read_text()));b=beta(parse(Path('/tmp/factor-low-goal-expr.txt').read_text()))
aliases={'`AspisR1S9LowOperatorShapeV1.E','`AspisR1S9NativeLowScalarArithmeticV1.E','`AspisR1S9ActualLowGenericWeightV1.E'}
quarter=parse('Lean.Expr.app (Lean.Expr.const `AspisR1S9NativeLowScalarArithmeticV1.embed []) (Lean.Expr.const `AspisR1S9ProductionPairCutV1.weights.QUARTER [])')
def norm(x):
 if isinstance(x,str):return '`AspisWideTower.WideExact'if x in aliases else x
 if tag(x,'const') and x[1]=='`AspisR1S9ActualLowGenericWeightV1.sourceQuarter':return quarter
 return [norm(y)for y in x]
a=norm(a);b=norm(b);diffs=[]
def diff(x,y,p='root'):
 if x==y:return
 if isinstance(x,str)or isinstance(y,str)or len(x)!=len(y):diffs.append((p,x,y));return
 for i,(xx,yy)in enumerate(zip(x,y)):diff(xx,yy,p+'.'+str(i))
diff(a,b);Path('/tmp/factor-low-expression-differences.json').write_text(json.dumps(diffs,indent=2));print('DIFFS',len(diffs));print(str(diffs)[:7000])
