#!/usr/bin/env python3
"""Audit the additive interface, its conditional boundary and focused receipts."""
from pathlib import Path
import hashlib, json, re, subprocess
R = Path(__file__).resolve().parents[2]
P = R/'docs/research/100bit-spend-path-20261013'
E = P/'evidence/s2-interface-20261022'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
source = P/'lean/S2LeadInterface.lean'
s = source.read_text()
record = s.split('structure S2CallerFacts',1)[1].split('/-- The SDK packet',1)[0]
fields = re.findall(r'^  (\w+) :',record,re.M)
expected = ['proofBytes','publicBytes','proofSuffix','proofLength','checkpointBytes',
            'checkpointLength','nodeViews','y1Input','observerNone','reachedPrefix',
            'callOrder','accountFrame','writtenMetadata','oracle']
assert fields == expected, fields
# This is a syntactic backstop to the explicit semantic review in FIELD-AUDIT.md.
assert not re.search(r'\b(?:eval|observe|run|Log|PushTrace|CallerInvariant|ClosedSum)\b',record)
assert not re.search(r'\b(?:sorry|admit|native_decide)\b|^\s*axiom\b|set_option\s+(?:maxHeartbeats|maxRecDepth)',s,re.M)
manifest = json.loads((E/'manifest.json').read_text())
accepted = [a for a in manifest['attempts'] if a['final_current']]
assert len(accepted) == 1
receipt = accepted[0]
assert receipt['source_sha256'] == sha(source)
assert receipt['exit'] == 0 and receipt['swaps'] == 0 and receipt['axioms_accepted']
for name in re.findall(r'^theorem (\w+)',s,re.M):
    assert any(a.split("'",2)[1].endswith('.'+name) for a in receipt['axioms']), name
for dep in receipt['direct_imports']:
    assert sha(dep['path']) == dep['sha256']
for dep in receipt['owned_transitive_dependencies']:
    assert sha(R/dep['source']) == dep['source_sha256'], dep['module']
changed = subprocess.check_output(['git','diff','--name-only','4f1631685'],cwd=R,text=True).splitlines()
changed += subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=R,text=True).splitlines()
allowed = [str(p.relative_to(R)) for p in [source,E,R/'tools/s2-interface-20261022',
    P/'design/S2-LEAD-INTERFACE-20261022.md',P/'design/HANDOFF-SESSION-A-20261021.md']]
assert all(any(f==a or f.startswith(a+'/') for a in allowed) for f in changed), changed
assert not any(f.endswith(('.olean','.elf','.tar','.tar.gz')) for f in changed)
result = {'schema':'s2-interface-audit-v1','source_sha256':sha(source),'fields':fields,
          'theorems_audited':len(re.findall(r'^theorem ',s,re.M)),
          'focused_compile_accepted':True,'conclusion_fields':[],
          's2_instantiated':False,'whole_frozen_join_established':False,
          'coherent_release_replay':False,'shipped_files_changed':False}
(E/'audit-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
