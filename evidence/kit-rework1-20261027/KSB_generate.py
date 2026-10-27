"""Restore raw release declarations; no shipped-function implementation model."""
from pathlib import Path
import hashlib, json, re

E = Path(__file__).resolve().parent
RAW = Path('evidence/extraction-assoc2-20261027/XRj_L013/sources/XRj_generated/XRh_Release/Funs.lean')
TYPES = Path('evidence/extraction-assoc2-20261027/XRj_L002/sources/XRj_generated/XRh_Release/Types.lean')
OLD = Path('evidence/extraction-assoc6-20261027')
def sha(b): return hashlib.sha256(b).hexdigest()
assert sha(RAW.read_bytes()) == 'f4b2d17c061ce7062d64146531788b6448328e656fb6dbd6192f2d61db31a3b5'
rows = []
def emit(name, s, source=None, inverse=None):
    p = E / (name + '.lean')
    p.write_text(s)
    row = dict(module=name, sha256=sha(p.read_bytes()), bytes=p.stat().st_size)
    if source:
        row.update(source=str(source), source_sha256=sha(source.read_bytes()))
    if inverse is not None:
        assert inverse == source.read_text(), name
        row['reverse_import_namespace_only_byte_identical'] = True
    rows.append(row)

# External *types* retained from the existing packet. These are carriers,
# not implementations; no claim of whole-kit or library fidelity is made.
s = (OLD/'XRn_Join_TypesExternal.lean').read_text()
pos=s.index('open Aeneas')
s=s[:pos]+'namespace KSB_Kit\n'+s[pos:]+'\nend KSB_Kit\n'
emit('KSB_Kit_TypesExternal',s,OLD/'XRn_Join_TypesExternal.lean')
for source,name,imports in [
    (TYPES,'KSB_Kit_Types',{'XRh_Release.TypesExternal':'KSB_Kit_TypesExternal'}),
    (RAW,'KSB_Kit_Funs',{'XRh_Release.Types':'KSB_Kit_Types','XRh_Release.FunsExternal':'KSB_Kit_Library'}),
]:
    original=source.read_text(); s=original
    for a,b in imports.items(): s=s.replace('import '+a+'\n','import '+b+'\n')
    # Isolate all generated names without editing any emitted declaration.
    pos=max(m.end() for m in re.finditer(r'(?m)^import [^\n]+\n',s))
    close=('\nend\n' if source==RAW else '')+'\nend KSB_Kit\n'
    s=s[:pos]+'\nnamespace KSB_Kit\n'+s[pos:]+close
    inverse=s.replace('\nnamespace KSB_Kit\n','',1).removesuffix(close)
    for a,b in imports.items(): inverse=inverse.replace('import '+b+'\n','import '+a+'\n')
    emit(name,s,source,inverse)

# All retained external functions here are std/core (including array/slice
# generated aliases). Exclude the entire shipped validator/expander tail.
p=OLD/'XRn_Join_FunsExternal.lean'; s=p.read_text().split('namespace XRn_Join_Bytes')[0]
s=s.replace('import XRn_Join_FieldExternal\n','').replace('import XRn_Join_Types\n','import KSB_Kit_Types\n')
s=s.replace('open XRn_Join_Release','open XRh_Release')
pos=s.index('open Aeneas'); s=s[:pos]+'namespace KSB_Kit\n'+s[pos:]+'\nend KSB_Kit\n'
emit('KSB_Kit_Library',s,p)
inventory=json.loads(Path('evidence/kit-audit1-20261027/KSA_inventory.json').read_text())
edits=[r for r in inventory['emitted_comparison'] if not r['equal_after_release_namespace_and_whitespace']]
assert len(edits)==15
receipt=dict(files=rows, restored_edited_declarations=edits,
    raw_funs_declarations=len(inventory['emitted_comparison']),
    emitted_body_policy='entire raw Funs byte-identical after reversing import/namespace wrappers',
    shipped_function_standins=0, library_fidelity='pending KSC work; no credit claimed',
    status='raw-body candidate; not a successful elaboration or closed kit')
raw=RAW.read_text(); new=(E/'KSB_Kit_Funs.lean').read_text()
spans=[]
for r in inventory['emitted_comparison']:
    m=re.search(r'(?m)^(?:@\[[^\n]*?\]\s*)*(?:def|abbrev)\s+'+re.escape(r['name'])+r'(?=\s|\{|\()',raw)
    assert m,r['name']
    spans.append((m.start(),r['name']))
spans.sort(); receipt['declaration_bytes']=[]
for i,(start,name) in enumerate(spans):
    stop=spans[i+1][0] if i+1<len(spans) else len(raw)
    span=raw[start:stop]
    assert span in new,name
    receipt['declaration_bytes'].append(dict(name=name,raw_start=start,raw_stop=stop,sha256=sha(span.encode()),exact_substring_present=True))
(E/'KSB_identity.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(dict(files=len(rows),restored=len(edits),raw_declarations=receipt['raw_funs_declarations'])))
