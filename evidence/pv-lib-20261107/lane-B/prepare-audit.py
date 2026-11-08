"""Existing strict private importAll audit; only root/module arrays change."""
import pathlib,re,json
E=pathlib.Path('evidence/pv-lib-20261107/lane-B')
modules=[];roots=[]
for p in sorted(pathlib.Path('lean').glob('PV_LIB_B_*.lean')):
 if p.stem.startswith('PV_LIB_B_RawAudit'):continue
 modules.append(p.stem)
 for n in re.findall(r'^#print axioms (\S+)',p.read_text(),re.M):roots.append(p.stem+'.'+n)
assert len(set(roots))==len(roots)
s=pathlib.Path('lean/PV_LIB_A_RawAudit16.lean').read_text()
start=s.index('    (#[`');stop=s.index('\n  let env ←',start)
s=s[:start]+'    (#['+', '.join('`'+n for n in modules)+'],\n     #['+', '.join('`'+n for n in roots)+'])'+s[stop:]
# Keep the accepted collector/walker and its two constructor summary candidates.
pathlib.Path('lean/PV_LIB_B_RawAudit5.lean').write_text(s)
(E/'AUDIT_ROOTS.json').write_text(json.dumps(dict(modules=modules,roots=roots,collector='PV_LIB_A_RawAudit16; arrays only changed',strict=True),indent=2)+'\n')
print(len(modules),'modules;',len(roots),'new roots')
