"""Generate/check focused audit roots; no package-wide replay."""
from pathlib import Path
import re,sys
R=Path(__file__).resolve().parents[2];D=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
groups={
 'PV_RJN_OrderAudit':['Bytes','Producers','PublishTrace','PublishOrder','NativePublishOrder','NodeContext','ContextPublishOrder','LayoutInstalled','InstalledPublishOrder'],
 'PV_RJN_NodeAudit':['NodeReject','NodeInstalled','NodeRangeWitness','NodeObstruction'],
 'PV_RJN_NativeAudit':['NativeNodeObstruction'],
}
for name,modules in groups.items():
 text=''.join('import R1Z.PV_RJN_'+m+'\n' for m in modules)
 text+='/-! Focused final audit; no full skeleton or release claim. -/\n'
 for m in modules:
  source=(D/('PV_RJN_'+m+'.lean')).read_text()
  for decl in re.findall(r'^(?:noncomputable )?(?:theorem|def|abbrev)\s+(\w+)',source,re.M):
   text+='#print axioms R1Z.PV_RJN_'+m+'.'+decl+'\n'
 path=D/(name+'.lean')
 if '--check' in sys.argv:assert path.read_text()==text,name
 else:path.write_text(text)
print('Audit roots checked' if '--check' in sys.argv else 'Audit roots generated')
