from pathlib import Path
import importlib.util,re
T=Path(__file__).parent;R=T.resolve().parents[1];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
sp=importlib.util.spec_from_file_location('w',T/'write-module.py');w=importlib.util.module_from_spec(sp);sp.loader.exec_module(w)
s=(L/'PV_RunJoin_CircleRawScalar52.lean').read_text();a=s.index('def field.M31.inv');b=s.index('def field.M31.sub',a);s=s[a:b]
ops=re.findall(r'let (\w+) ← field\.(M31.mul|square_n) ([^\n]+)',s)
ops.append(('out','M31.mul','m7 self'))
body='''open PV_RunJoin_CircleNeutralShape53

theorem nonzero (self : U32) (hcself : Canon self) (hne : (self != 0#u32)=true) :
    ∃ y, PV_RunJoin_CircleRawScalar52.field.M31.inv self = ok y ∧
      PV_RunJoin_CircleR72Raw52.field.M31.inv self = ok y ∧ Canon y := by
'''
for i,(n,op,args) in enumerate(ops):
 aa=args.split()
 if op=='M31.mul':call='PV_RunJoin_CircleNeutralMul53.complete '+args+' hc'+aa[0]+' hc'+aa[1]
 else:call='PV_RunJoin_CircleNeutralSquareN53.complete '+aa[0]+' hc'+aa[0]+' '+aa[1]
 body+=f'  obtain ⟨{n},h{i},h{i}\',hc{n}⟩ := {call}\n'
body+='  refine ⟨out,?_,?_,hcout⟩\n'
for raw,suffix in [('PV_RunJoin_CircleRawScalar52',''),('PV_RunJoin_CircleR72Raw52',"'")]:
 body+='  · unfold '+raw+'.field.M31.inv\n    simp only [massert,hne,bind_tc_ok,'+','.join('h'+str(i)+suffix for i in range(len(ops)))+']\n'
w.write('PV_RunJoin_CircleNeutralInvNonzero53',['R1Z.PV_RunJoin_CircleNeutralSquareN53'],body,['nonzero'])
