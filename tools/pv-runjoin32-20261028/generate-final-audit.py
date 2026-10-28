from pathlib import Path
import json,re,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin32-20261028';p=R/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_FinalAudit32.lean'
mods=sorted({v['module'] for q in E.glob('modules-*.json') for v in json.loads(q.read_text()) if v['accepted'] and v['module'].endswith('32') and v['module']!='R1Z.PV_RunJoin_FinalAudit32'})
source=''.join('import '+m+'\n' for m in mods)+'\n/-! Final focused audit of accepted runjoin32 proof additions. The endpoint,\nlane and NativeSnapshot31 audits have their separate once-only receipts.\nThis audit neither installs a runtime nor discharges the retained P laws. -/\n'
prints=[]
for m in mods:
 s=(R/'docs/research/v8-r0-zk-20261009/lean'/(m.replace('.','/')+'.lean')).read_text()
 for match in re.finditer(r'^#print axioms (\S+)\s*$',s,re.M):
  n=match[1];full=n if n.startswith('R1Z.') else m+'.'+n
  if full not in prints:prints.append(full)
source+=''.join('#print axioms '+n+'\n' for n in prints)
if '--check' in sys.argv:assert p.read_text()==source
else:p.write_text(source)
(E/'final-audit-scope.json').write_text(json.dumps(dict(modules=mods,printed_declarations=prints,new_axioms_permitted=['propext','Classical.choice','Quot.sound']),indent=2)+'\n')
print('final audit symbolic preflight:',len(mods),'modules,',len(prints),'declarations')
