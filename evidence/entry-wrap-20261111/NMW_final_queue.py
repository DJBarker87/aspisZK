from NMW_formal import *
r=run('NMW_L026','lean','NMW_COMBINED_IMPORT');assert r['exit_status']==0
files={n:(E/n).read_text() for n in ['NMW_batch.py','NMW_AUDIT_ROOTS.json','NMW_AUDIT_MODULES.json']}
r=run('NMW_L027','audit','proof5',['python3','NMW_batch.py','proof5'],files);assert r['exit_status']==0
