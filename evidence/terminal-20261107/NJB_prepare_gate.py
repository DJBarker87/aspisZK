from pathlib import Path
import json,re,difflib
E=Path(__file__).resolve().parent;P=E.parent/'ledger13-20261107'
for name in ['Driver','ProofDriver']:
 s=(P/f'NIU_{name}.lean').read_text();t=s.replace('NIU_','NJB_');(E/f'NJB_{name}.lean').write_text(t);(E/f'NJB_{name}.diff').write_text(''.join(difflib.unified_diff(s.splitlines(True),t.splitlines(True),fromfile='NIU_'+name,tofile='NJB_'+name)))
# Original walker and memory instrumentation remain untouched. Only driver runtime names change.
(E/'NJB_gate_setup.py').write_text('''from pathlib import Path
import hashlib,json,shutil
b=Path.cwd();p=Path('/home/dombarker/project-offloads/codex-cx-ledger13-20261107/NIU_native');rows=[]
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 q=p/n;r=b/'NJB_native'/n;shutil.copyfile(q,r);rows.append(dict(source=str(q),target=str(r),sha256=hashlib.sha256(r.read_bytes()).hexdigest(),bytes=r.stat().st_size))
(b/'NJB_GATE_PINS.json').write_text(json.dumps(rows,indent=1));print('unchanged walker/memory C source copied and pinned')
''')
base=json.loads((E/'NJB_L073.json').read_text());base.update(attempt='NJB_L076',module='NJB_gate_setup',sources=['NJB_gate_setup.py'],command=['python3','NJB_gate_setup.py'],collect=['NJB_GATE_PINS.json']);(E/'NJB_L076.json').write_text(json.dumps(base))
