from pathlib import Path
import json,hashlib,lzma,re
E=Path('/Users/dominic/ZK/.worktrees/cx-ledger14/evidence/entry-leaves-20261107')
sha=lambda b:hashlib.sha256(b).hexdigest()
idx=json.loads((E/'NJH_INPUTS.json').read_text());count=0
for h,row in idx['objects'].items():
 p=E/row['path'];raw=lzma.decompress(p.read_bytes());assert sha(raw)==h and len(raw)==row['bytes'];assert sha(p.read_bytes())==row['archive_sha256'];count+=1
ats=[json.loads(l) for l in (E/'NJH_ATTEMPTS.jsonl').read_text().splitlines()]
for r in ats:
 a=r['attempt'];ad=json.loads((E/(a+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True
 for n,h in r['source_hashes'].items():assert idx['attempts'][a][n]==h,(a,n)
 assert int(r['swaps'])==0
 if a.startswith('NJH_K'):
  g=json.loads((E/(a+'-graph-check.json')).read_text());lock=json.loads((E/(a+'-lock-check.json')).read_text());assert lock['unchanged']
for a in [5,7,9,11,13]:
 s=lzma.decompress((E/f'NJH_K{a:03}'/'stdout.log.xz').read_bytes()).decode()
 assert 'VERIFICATION:- FAILED' in s and 'Failed Checks:' in s
for n in ['NJH_Observer','NJH_Ref.Types','NJH_Ref.Funs','NJH_BorrowLaws','NJH_BorrowCounters','NJH_BorrowModel','NJH_SyscallLaws','NJH_ReplyComposition','NJH_CopyWindow','NJH_LaneIterator','NJH_COMBINED_IMPORT']:
 h=sha((E/(n+'.lean')).read_bytes());assert any(r['module']==n and r['exit_status']==0 and h in r['source_hashes'].values() for r in ats),n
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\s', (E/(n+'.lean')).read_text(),re.M)
assert not list(E.rglob('__pycache__'))
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024]
x=dict(status='PASS',pinned_inputs=count,attempts=len(ats),admissions='all exit0 AND allowed:true',negative_controls='intended assertion failures, not timeouts or compilation failures',current_accepted_sources='all match successful receipts',over20MB=0,source_changes='NJH evidence only',target_established=False)
(Path('/Users/dominic/ZK/.worktrees/cx-ledger14/evidence/ledger14-20261108/NJK_NJH_REVALIDATION.json')).write_text(json.dumps(x,indent=1)+'\n');print(json.dumps(x))
