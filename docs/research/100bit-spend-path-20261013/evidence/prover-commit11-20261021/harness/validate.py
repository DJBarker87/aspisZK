#!/usr/bin/env python3
"""Validate literal source, receipt, and deletion evidence; never replay Lean."""
from pathlib import Path
import json,hashlib,re,sys,difflib
E=Path(__file__).resolve().parent.parent
ROOT=E.parents[4]
M=json.loads((E/'manifest.json').read_text())
for path,sha in M['sources'].items():
    assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==sha,path
rows=[]
for p in sorted((E/'lean').glob('attempts-*.jsonl')):
    rows += [json.loads(x) for x in p.read_text().splitlines()]
byid={r['attempt']:r for r in rows}
assert len(byid)==len(rows)
for a,r in byid.items():
    snap=E/'lean/sources'/f"attempt-{a}-{Path(r['module']).stem}.lean.txt"
    assert hashlib.sha256(snap.read_bytes()).hexdigest()==r['source_sha256']
    assert hashlib.sha256(json.dumps(r['deps'],sort_keys=True).encode()).hexdigest()==r['deps_fingerprint']
    if r['accepted']:
        assert r['exit_status']==0 and r['swaps']==0
        for line in r['axioms']:
            if 'depends on axioms:' in line:
                used=set(re.search(r'\[([^]]*)\]',line,re.S)[1].replace('\n','').replace(' ','').split(','))
                assert used <= {'propext','Classical.choice','Quot.sound'},line
if '--check' not in sys.argv:
    audit=byid[M['audit_attempt']]
    assert audit['accepted']
    names=[re.search(r"'([^']+)'",line)[1] for line in audit['axioms']]
    assert names==M['public_axiom_targets']
for module,a in M['adopted'].items():
    r=byid[a];assert r['accepted']
    p=ROOT/'docs/research/v8-r0-zk-20261009/lean'/r['module']
    assert hashlib.sha256(p.read_bytes()).hexdigest()==r['source_sha256']
    assert p.stem==module.split('.')[-1]
before=(E/'headline-before.lean.txt').read_text();after=(E/'headline-after.lean.txt').read_text()
diff=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='headline-before.lean',tofile='headline-after.lean'))
assert diff==(E/'headline-deletions.diff').read_text()
assert not any(s.startswith('+') and not s.startswith('+++') for s in diff.splitlines())
assert sum(s.startswith('-') and not s.startswith('---') for s in diff.splitlines())==2
assert after==(ROOT/'docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineOwnedClosed.lean').read_text()
for p in [ROOT/x for x in M['sources'] if x.endswith('.lean')]:
    assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b|set_option max(RecDepth|Heartbeats)',p.read_text()),p
print(f"Validated {len(M['sources'])} frozen sources, {len(M['adopted'])} adopted modules, {len(rows)} attempts, and the deletion-only diff.")
