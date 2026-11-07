from NMV_formal import *
import re
mods=['NMV_CandidateRoots','NMV_NNCWeak']
roots=[]
for m in mods:
 s=(E/(m+'.lean')).read_text();ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 names=re.findall(r'^(?:theorem|def) (\w+)',s,re.M)
 assert set(names)==set(re.findall(r'^#print axioms (\w+)',s,re.M))
 roots += [ns+'.'+n for n in names]
if sys.argv[1]=='combined':
 p=E/'NMV_CONTROLS_COMBINED_IMPORT.lean'
 p.write_text('import NMV_BN_COMBINED_IMPORT\n'+''.join('import '+m+'\n' for m in mods)+'\n'+''.join('#print axioms '+r+'\n' for r in roots))
 rc=run('NMV_L126','lean','NMV_CONTROLS_COMBINED_IMPORT');sys.exit(rc['exit_status'])
if sys.argv[1]=='audit':
 manifest=json.loads((E/'NMV_AUDIT_ROOTS.json').read_text());groups=json.loads((E/'NMV_AUDIT_MODULES.json').read_text())
 assert all(n not in manifest['roots'] for n in roots)
 g=len(groups);manifest['groups'].append(roots);manifest['roots']+=roots;groups.append(mods)
 (E/'NMV_AUDIT_ROOTS.json').write_text(json.dumps(manifest,indent=1)+'\n')
 (E/'NMV_AUDIT_MODULES.json').write_text(json.dumps(groups,indent=1)+'\n')
 (E/'NMV_RESUME_ROOTS.json').write_text(json.dumps(dict(roots=roots,modules=mods,group=g),indent=1)+'\n')
 files={n:(E/n).read_text() for n in ['NMV_batch.py','NMV_AUDIT_ROOTS.json','NMV_AUDIT_MODULES.json']}
 rc=run('NMV_L127','audit','proof'+str(g),['python3','NMV_batch.py','proof'+str(g)],files);sys.exit(rc['exit_status'])
raise ValueError(sys.argv[1])
