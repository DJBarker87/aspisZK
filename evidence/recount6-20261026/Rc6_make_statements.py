from pathlib import Path
import re
L=Path('lean');a=(L/'Rc5_Top.lean').read_text();b=(L/'Rc6_Top.lean').read_text()
header=b.split('/-- Composed adopted')[0].replace('namespace AspisR1.Rc6_Top','namespace AspisR1.Rc6_Statements')
def parts(s):
 t=s.split('theorem deployed ',1)[1].split(' := by',1)[0]
 bind,concl=t.split(' :\n    ',1)
 return bind,concl
ab,ac=parts(a);bb,bc=parts(b);assert ab==bb
# Strip explicit hypothesis binders? Keep all; full before/after statement exact and reviewable.
names=[]
for m in re.finditer(r'^    \((\w+(?: \w+)*)\s*:',ab,re.M):names.extend(m[1].split())
args=' '.join(names)
# w1 e1 etc multiple line arguments: header grouped binder start includes L etc; regex complete.
Path('evidence/recount6-20261026/Rc6_binder_names.txt').write_text(args+'\n')
app='L e1 e2 w1 w2 (Rc5_Install.configuration indexError c reservation).adapter (Rc5_Install.configuration indexError c reservation).currentBase (Rc5_Install.configuration indexError c reservation).reserved (Rc5_Install.configuration indexError c reservation).query (Rc5_Install.configuration indexError c reservation).geometry (Rc5_Install.configuration indexError c reservation).stageBase (Rc5_Install.configuration indexError c reservation).finish c.boundaries reservation CPH_Program.verifier data1 data2 slot saved post1 post2 H (DrvC_Implementation.driver (Rc5_Install.configuration indexError c reservation)) prior (p.physicalEvents t)'
proof=''' := by
  obtain ⟨p6,driverEq,sdkEq,result,headline,bound,zero,copyFacts,events,protection,trace,recorder⟩ := after
  exact ⟨driverEq,sdkEq,Rc6_Forget.forget APP hashv result,headline,bound,zero,
    copyFacts,events,protection,trace,recorder⟩
'''.replace('APP',app)
# duplicate only conclusion with identical binder context; no opaque aliases hiding input changes.
Path('lean/Rc6_Statements.lean').write_text('import Rc6_Forget\n'+header+'theorem reverse '+bb+'\n    (after :\n    '+bc+') :\n    '+ac+proof+'\n#print axioms reverse\nend AspisR1.Rc6_Statements\nend\n')
Path('evidence/recount6-20261026/Rc6_before-statement.lean.txt').write_text('theorem deployed '+ab+' :\n    '+ac+'\n')
Path('evidence/recount6-20261026/Rc6_after-statement.lean.txt').write_text('theorem deployed '+bb+' :\n    '+bc+'\n')
