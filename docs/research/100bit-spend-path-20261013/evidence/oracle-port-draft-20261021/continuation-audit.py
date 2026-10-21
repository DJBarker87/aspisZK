#!/usr/bin/env python3
"""Audit continuation receipts and signatures without replaying Lean."""
from pathlib import Path
import hashlib,json,difflib,re,subprocess
root=Path(__file__).resolve().parents[5]
base=root/'docs/research/100bit-spend-path-20261013'
ev=Path(__file__).resolve().parent
subprocess.run(['python3','-B',str(ev/'audit.py')],cwd=root,check=True)
all_attempts=json.loads((ev/'manifest.json').read_text())['attempts']
attempts=[r for r in all_attempts if r['module'].endswith('Draft')]
latest={r['module']:r for r in attempts}
assert len(latest)==12,sorted(latest)
for r in latest.values():assert r['exit']==0
before=(ev/'prefix-headline-before.lean.txt').read_text()
after=(ev/'prefix-headline-after.lean.txt').read_text()
binder='    (hcompletion : OraclePortConsumer.Completion D (admit core) P (Q + 1161))\n'
assert before.replace(binder,'')==after and before.count(binder)==1
src=(base/'lean/OraclePortPrefixHeadlineDraft.lean').read_text()
a=src.index('theorem final_soundness\n');z=src.index(' := by',a)
assert after==src[a:z]+'\n'
generic=(base/'lean/OraclePortHeadline.lean').read_text()
a=generic.index('theorem final_soundness\n');z=generic.index(' := by',a)
specialized=generic[a:z].replace('(dO : Decision)','(core : Decision)')
specialized=re.sub(r'\bdO\b','(admit core)',specialized)+'\n'
assert before==specialized,'Before signature must be the literal admitted specialization'
assert (ev/'prefix-completion-deletion-only.diff').read_text()==''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='admitted-generic-before',tofile='admitted-generic-after'))
src=(base/'lean/OraclePortReaderSourceDraft.lean').read_text()
a=src.index('def ReaderBinding');z=src.index('\ntheorem typed_binding_implies',a)
assert (ev/'reader-binding-replacement.lean.txt').read_text()==src[a:z]+'\n'
for row in subprocess.check_output(['git','diff','--name-status','8bf459d0d'],cwd=root,text=True).splitlines():
    status,path=row.split('\t',1)
    if '/lean/' in path:assert status=='A' and Path(path).name.startswith('OraclePort'),row
fail=[r for r in attempts if r['exit']!=0]
review=json.loads((ev/'data-choice-resource-review.json').read_text())
assert review['cap_raised'] is False and review['unchanged_retry'] is False
result={'scope':'Focused cache-based continuation; frozen dV remains incomplete',
    'modules':sorted(latest),'module_count':len(latest),'attempts':len(attempts),
    'failed_attempts':len(fail),'final_axiom_reports':sum(len(r['axioms']) for r in latest.values()),
    'peak_final_rss_bytes':max(r['peak_rss_bytes'] for r in latest.values()),
    'process_swaps':sum(r['swaps'] or 0 for r in attempts),
    'memory_failures':[r['module']+'-'+str(r['attempt']) for r in fail if r['exit']<0],
    'new_admitted_headline_deleted_binder':binder.strip(),
    'old_headline_deletions':0,
    'remaining':['checkpoint state construction and resume composition','66-leaf total budget law','acceptance-to-reader-typed-arithmetic transfer','frozen Rust/caller equality','shifted M10 ledger','source/runtime/release boundaries'],
    'final_receipts':[{k:r[k] for k in ['module','attempt','exit','wall_seconds','peak_rss_bytes','swaps','source_revision','source_sha256','deps_fingerprint','axioms']} for r in latest.values()]}
(ev/'continuation-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='final_receipts'},indent=2))
