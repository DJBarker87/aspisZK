from NNE_formal import *
mods=json.loads((E/'NNE_RESUME_MODULES.json').read_text());mods.remove('NNE_Inspect')
(E/'NNE_RESUME_MODULES.json').write_text(json.dumps(mods,indent=1)+'\n')
roots=json.loads((E/'NNE_RESUME_ROOTS.json').read_text())
r=json.loads((E/'NNE_AUDIT_ROOTS.json').read_text());assert len(r['groups'])==1
r['groups'].append(roots);(E/'NNE_AUDIT_ROOTS.json').write_text(json.dumps(r,indent=1)+'\n')
m=json.loads((E/'NNE_AUDIT_MODULES.json').read_text());assert len(m)==1
m.append(mods);(E/'NNE_AUDIT_MODULES.json').write_text(json.dumps(m,indent=1)+'\n')
(E/'NNE_RESUME_COMBINED_IMPORT.lean').write_text('import NNE_COMBINED_IMPORT\nimport NNE_PhysicalTop\nimport NNE_SelectedContext\nimport NNE_Clock\nimport NNE_TraceInstantiation\n')
rc=run('NNE_L096','lean','NNE_RESUME_COMBINED_IMPORT')
if rc['exit_status']:sys.exit(rc['exit_status'])
files={n:(E/n).read_text() for n in ['NNE_batch.py','NNE_AUDIT_ROOTS.json','NNE_AUDIT_MODULES.json']}
rc=run('NNE_L097','audit','proof1',['python3','NNE_batch.py','proof1'],files)
sys.exit(rc['exit_status'])
