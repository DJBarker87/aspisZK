from NLA_formal import *
r=run('NLA_L027','cache','NLA_RetainedExport',['python3','NLA_export.py'],extra={'NLA_export.py':(E/'NLA_export.py').read_text()});assert r['exit_status']==0
r=ssh('python3',f"from pathlib import Path;print(Path({B!r},'NLA_EXPORT.json').read_text())");assert r.returncode==0
(E/'NLA_EXPORT.json').write_text(r.stdout)
print('NLA retained export recorded')
