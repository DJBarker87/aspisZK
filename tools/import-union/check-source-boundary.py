#!/usr/bin/env python3
"""Check exact migration edits and invariant existing proof statements/definitions."""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
ROOT=Path(__file__).resolve().parents[2]
E=ROOT/'docs/research/100bit-spend-path-20261013/evidence/import-union-20261022'
BASE='317a687e34^'
sha=lambda b:hashlib.sha256(b).hexdigest()
spec=importlib.util.spec_from_file_location('migration',ROOT/'tools/import-union/migrate.py')
migration=importlib.util.module_from_spec(spec);spec.loader.exec_module(migration)
rows=json.loads((E/'migration.json').read_text())['files']
for r in rows:
    before=subprocess.check_output(['git','show',BASE+':'+r['path']],cwd=ROOT)
    after=(ROOT/r['path']).read_bytes()
    assert migration.transform(before)==(after,r['attributes']),r['path']
    assert sha(before)==r['before_sha256'] and sha(after)==r['after_sha256'],r['path']
changed=subprocess.check_output(['git','diff','--name-only',BASE,'HEAD'],cwd=ROOT,text=True).splitlines()
assert all('/lean-candidates/' not in p for p in changed),'candidate edit'
assert all(p.startswith(('docs/research/','tools/import-union/')) for p in changed),'shipped edit'
starts=re.compile(r'(?m)^(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(?:theorem|def|abbrev|structure|inductive|class|instance|namespace|end|attribute|set_option|import|#print)\b')
def surface(text):
    positions=[m.start() for m in starts.finditer(text)]+[len(text)]
    result=text[:positions[0]] if positions else text
    statements={}
    for a,b in zip(positions,positions[1:]):
        block=text[a:b]
        hit=re.match(r'(?:(?:private|protected)\s+)*theorem\s+(\S+)',block)
        if hit:
            assert ':=' in block,hit[1]
            header=block.split(':=',1)[0]
            statements[hit[1]]=header.split()
            result+=header+' := CHECKED_PROOF\n'
        elif not block.startswith(('import ','#print axioms ')):
            result+=block
    return result.split(),statements
migrated={r['path'] for r in rows}
repairs=[]
for p in changed:
    if not p.endswith('.lean') or '/lean/' not in p or p in migrated:continue
    old=subprocess.run(['git','show',BASE+':'+p],cwd=ROOT,capture_output=True)
    if old.returncode:continue
    before=old.stdout.decode();after=(ROOT/p).read_text()
    old_surface,old_statements=surface(before);new_surface,new_statements=surface(after)
    assert old_statements==new_statements,('theorem statement changed',p)
    assert old_surface==new_surface,('non-proof definition changed',p)
    repairs.append({'path':p,'before_sha256':sha(old.stdout),'after_sha256':sha(after.encode()),
                    'theorem_statements_identical':True,'existing_nonproof_declarations_identical':True,
                    'theorems':sorted(old_statements)})
(E/'source-boundary-check.json').write_text(json.dumps({'migration_files_verified':len(rows),
 'migration_attributes_verified':sum(r['attributes'] for r in rows),'candidate_edits':False,
 'shipped_edits':False,'research_proof_or_import_repairs':repairs},indent=2,sort_keys=True)+'\n')
print('exact migrations',len(rows),'proof/import-only repairs',len(repairs),'candidate/shipped edits: zero')
