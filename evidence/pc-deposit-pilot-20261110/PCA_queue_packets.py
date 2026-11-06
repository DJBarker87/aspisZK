from PCA_formal import run, E
import json
mods=['PCA_Borrow','PCA_Packet']+[f"PCA_RowSpec_POOL_{int(r['row'].split(':')[1])}" for r in json.loads((E/'PCA_CHILDREN.json').read_text())['direct_pool_children']]
for a,m in enumerate(mods,15):
 r=run(f'PCA_L{a:03d}','lean',m)
 if r['exit_status']:raise SystemExit(r['exit_status'])
