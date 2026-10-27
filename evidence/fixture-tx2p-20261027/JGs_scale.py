from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2]
p=R/'evidence/fixture-tx2o-20261027/JGq_scale.py'
s=p.read_text();s=s[:s.index('for mod,t in out.items():')]
out={}
for k in [1,3,4]:
 env={'__file__':str(p)}
 src=s.replace("row=x['nums']('JGo_TX2_WeightData',f'f0{tag}')",f"row=x['nums']('JGo_TX2_WeightData',f'f{k}{{tag}}')").replace("mod=f'JGq_Scale{tag}'",f"mod=f'JGs_S{k}{{tag}}'").replace('JGo_TX2_WeightData.f0{tag}',f'JGo_TX2_WeightData.f{k}{{tag}}')
 exec(src,env);out.update(env['out'])
for mod,s in out.items():
 p=R/'lean'/(mod+'.lean')
 if '--check' in sys.argv:assert p.read_text()==s,mod
 else:p.write_text(s)
print(len(out),'scalar modules')
