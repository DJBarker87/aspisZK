"""Validate the draft against retained evidence, without invoking a prover."""
import csv
import hashlib
import json
import re
import resource
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path
from urllib.parse import unquote

started = time.monotonic()
ROOT = Path(__file__).resolve().parents[2]
OUT = Path(__file__).resolve().parent
BASE = '0fb28ae24b1a3c72a59260cad5d95908dac18f04'
DOC = ROOT/'design/TRUST-INVENTORY-APPENDIX-DRAFT-20261027.md'
AUDIT = ROOT/'evidence/l188-audit1-20261027'
def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True).strip()
def pin(p):
    b=p.read_bytes()
    return {'sha256': hashlib.sha256(b).hexdigest(), 'bytes': len(b)}
s=DOC.read_text()
assert '<!-- CIa_' not in s
fields=json.loads((AUDIT/'L8a_TrustFieldMap.json').read_text())
field_section=s.split('## One-to-one named-field inventory')[1].split('## Definition-level and external surfaces')[0]
table=[l for l in field_section.splitlines() if l.startswith('| `AspisR1.')]
assert len(table)==44
assert Counter(re.match(r'\| `([^`]+)`', l)[1] for l in table)==Counter(r['field'] for r in fields)
for r in fields:
    row=next(l for l in table if l.startswith('| `'+r['field']+'`'))
    expected='NAMED-IN-CONTRACT' if r['contract_literal_name_present'] else 'ACCEPTED-ELSEWHERE'
    assert '**'+expected in row
    # Reuse fresh prints to confirm every projection name, not cached spelling guesses.
    assert r['field'] in (AUDIT/'L8a_008/stdout.log').read_text()
surfaces=json.loads((AUDIT/'L8a_SurfaceClassification.json').read_text())
assert len(surfaces)==len({r['name'] for r in surfaces})==9224
with (OUT/'CIa_UnrecordedAxioms.tsv').open() as f:
    unrecorded=list(csv.DictReader(f,delimiter='\t'))
assert len(unrecorded)==105
assert {r['declaration'] for r in unrecorded}=={r['name'] for r in surfaces if r['classification'].startswith('F-AXIOM:')}
assert all(r['status']=='UNRECORDED' and r['Rc10_reachable']=='False' and r['ARX_reachable']=='False' for r in unrecorded)
links=[]
for target in re.findall(r'\]\(([^)]+)\)', s):
    if '://' in target: continue
    local=unquote(target.split('#')[0]); dest=DOC.parent/local
    assert dest.exists(), target
    links.append(target)
protected=[
 'docs/research/100bit-spend-path-20261013/design/SECURITY-CONTRACT-20261021.md',
 'design/PREMISE-LEDGER-20261025.md',
 'lean/Rc10_Top.lean','lean/ARX_Root.lean']
for rel in protected:
    assert (ROOT/rel).read_bytes()==subprocess.check_output(['git','show',f'{BASE}:{rel}'],cwd=ROOT), rel
# Exhaust the changed-file set, including staged/unstaged tracked content.
changed=git('diff','--name-only',BASE).splitlines()
assert all(p==str(DOC.relative_to(ROOT)) or p.startswith('evidence/contract-inventory1-20261027/CIa_') for p in changed)
subprocess.run(['git','diff','--check',BASE],cwd=ROOT,check=True)
# Fresh audit before/after statement evidence is reused, not regenerated.
for root in ['Rc10_Top','ARX_Root']:
    assert (AUDIT/f'L8a_{root}.BEFORE.statement.txt').read_bytes()==(AUDIT/f'L8a_{root}.AFTER.statement.txt').read_bytes()
source_inputs=[DOC, AUDIT/'L8a_TrustAudit.md', AUDIT/'L8a_TrustFieldMap.json',
 AUDIT/'L8a_SurfaceClassification.json', AUDIT/'L8a_008/stdout.log',
 ROOT/protected[0], ROOT/'design/TRUST-AUDIT-20261026.md',
 ROOT/'design/SECURITY-CONTRACT-ARX-AMENDMENT-DRAFT-20261027.md',
 ROOT/'design/RUNTIME-PERSISTENCE-ITEM-20261026.md',
 ROOT/'docs/research/100bit-spend-path-20261013/design/L166-DECISION-20261027.md',
 ROOT/'docs/research/100bit-spend-path-20261013/design/D188-PROVENANCE-FINDING-20261027.md',
 ROOT/'docs/research/100bit-spend-path-20261013/design/C3-BIN-20261021.md',
 ROOT/'docs/research/v8-r0-zk-20261009/LOG.md', Path(__file__), OUT/'CIa_UnrecordedAxioms.tsv']
reuse=[]
for a in ['L8a_006','L8a_007','L8a_008']:
    p=AUDIT/a/'receipt.json'; r=json.loads(p.read_text())
    assert r['exit_status']==0
    reuse.append({'receipt':str(p.relative_to(ROOT)), **pin(p),
      **{k:r[k] for k in ['module','source_revision','source_hashes','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','limits','print_axioms']}})
usage=resource.getrusage(resource.RUSAGE_SELF)
result={
 'kind':'offline documentation reconciliation, not a formal release result',
 'source_revision':git('rev-parse','HEAD'),'baseline_revision':BASE,
 'branch':git('branch','--show-current'),
 'branch_discrepancy':'Assigned 20261026 branch absent; existing assigned worktree is on 20261027 branch; no branch switch or other worktree edit.',
 'target':str(DOC.relative_to(ROOT)),'exit_status':0,
 'wall_seconds':time.monotonic()-started,
 'peak_rss':usage.ru_maxrss,'peak_rss_unit':'bytes' if sys.platform=='darwin' else 'KiB',
 'swaps':usage.ru_nswap,'scope':'none; no Lean/Rust/Kani/build executed',
 'lean_attempts_used':0,'lean_attempts_budget':5,'kani_runs':0,
 'print_axioms':'not applicable: no new theorem; retained clean audits below',
 'named_fields':44,'field_statuses':{'NAMED-IN-CONTRACT':sum(r['contract_literal_name_present'] for r in fields),'ACCEPTED-ELSEWHERE_including_7_historical_interfaces':sum(not r['contract_literal_name_present'] for r in fields)},
 'surface_classes':dict(Counter(r['classification'] for r in surfaces)),
 'unrecorded_axioms':105,'local_links_checked':len(links),
 'protected_files_unchanged':protected,
 'premise_delta':{'removed':0,'added':0,'reclassified':0},
 'nonvacuity':'unchanged conditional ARX theorem; no joint accepted-pair inhabitant claimed',
 'artifact_evidence':'inherited H5 pins only; no rebuild trigger; no shipped source changed',
 'input_pins':{str(p.relative_to(ROOT)):pin(p) for p in source_inputs},
 'reused_lean_receipts':reuse,
 'checks':'PASS: all 44 names present in fresh L8a_008 prints, exact field coverage/statuses, 105 individual findings, declaration count, local links, unchanged protected files/statements, allowed file scope, diff whitespace'
}
(OUT/'CIa_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['checks','named_fields','unrecorded_axioms','local_links_checked','lean_attempts_used','branch','wall_seconds']},indent=2))
