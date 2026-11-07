#!/usr/bin/env python3
"""Run the unchanged NKT sites() pattern checker on reproduced batch emission."""
from pathlib import Path
import ast,re,json,hashlib
E=Path(__file__).resolve().parent;source=(E.parent/'emission-audit-20261109/NKT_checker.py').read_text();tree=ast.parse(source);node=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='sites');code=ast.get_source_segment(source,node);ns={'re':re};exec(compile(code,'NKT_checker.py::sites','exec'),ns)
p=E/'NMH_E010_emitted/raw/NJS_Extract/Funs.lean';raw=p.read_bytes();hits=ns['sites'](raw.decode());selected=[h for h in hits if 'batch_tree' in h['definition']]
assert any(len(h['done_none'])>=4 for h in selected)
(E/'NMH_BC_CROSSREFERENCE.json').write_text(json.dumps(dict(checker_source='evidence/emission-audit-20261109/NKT_checker.py',checker_function_sha256=hashlib.sha256(code.encode()).hexdigest(),emission=str(p.relative_to(E)),emission_sha256=hashlib.sha256(raw).hexdigest(),findings=selected,classification='Known NKT-F1/(bc) pattern reproduced; no new native-fidelity or row verdict'),indent=2)+'\n')
print('Known NKT-F1 post-loop done-none pattern retained in reproduced raw batch emission')
