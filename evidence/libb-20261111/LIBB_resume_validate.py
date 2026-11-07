"""Validate only this authorized continuation's immutable receipts and roots."""
from pathlib import Path
import json,hashlib,re,lzma,subprocess
E=Path(__file__).resolve().parent
rows=[]
for d in sorted(E.glob('LIBB_L3[0-9][0-9]')):
 if not d.is_dir() or int(d.name[-3:])<301:continue
 p=d/'receipt.json'
 if not p.exists():continue
 r=json.loads(p.read_text());a=r['attempt'];rows.append(r)
 assert r['kind'] in ['lean','audit','link'],a
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
 assert int(r['swaps'])==0,a
 ad=json.loads((E/(a+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True,a
 disks=[json.loads(p.read_text()) for p in E.glob(a+'-disk-*.json')];assert disks[-1]['free']>=40_000_000_000,a
 for name,sha in r['source_hashes'].items():assert hashlib.sha256((d/'sources'/name).read_bytes()).hexdigest()==sha,(a,name)
 assert r['source_revision'],a
 if r['exit_status']==0:
  assert 'sorryAx' not in (d/'stdout.log').read_text(),a
attempts=[json.loads(l) for l in (E/'LIBB_ATTEMPTS.jsonl').read_text().splitlines()]
for r in rows:
 checks=[x for x in attempts if x.get('attempt')==r['attempt'] and x.get('event')=='share_check'];assert checks and checks[-1]['host']['count']<6,r['attempt']
expected=json.loads((E/'LIBB_RESUME_AUDITS.json').read_text());coverage=[]
standard={'propext','Classical.choice','Quot.sound'}
for group in expected:
 p=E/'LIBB_audit'/group['mode']/(group['mode']+'.json')
 assert p.exists(),str(p)
 a=json.loads(p.read_text());assert a['exit_status']==0
 assert set(x['root']for x in a['results'])==set(group['roots'])
 for row in a['results']:
  assert row['equal'] is True,row
  assert set(row['collect_axioms'])==set(row['walked_axioms'])<=standard,row
  raw=E/('LIBB_NEP_'+group['mode']+'_'+row['root']+'_REACHABLE.txt')
  data=lzma.decompress(raw.with_suffix(raw.suffix+'.xz').read_bytes())
  assert hashlib.sha256(data).hexdigest()==raw.with_suffix(raw.suffix+'.sha256').read_text().strip(),row['root']
  coverage.append(dict(root=row['root'],module=group['module'],raw=str(raw.name)+'.xz',axioms=row['walked_axioms'],equal=True))
assert len(coverage)==40
for g in expected:
 source=(E/(g['module']+'.lean')).read_text()
 assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b',source),g['module']
 for root in g['roots']:assert '#print axioms '+root.split('.')[-1] in source,root
 accepted=[r for r in rows if r['kind']=='lean' and r['module']==g['module'] and r['exit_status']==0]
 assert accepted,g['module']
 assert accepted[-1]['source_hashes']['LIBB_generated/'+g['module']+'.lean']==hashlib.sha256(source.encode()).hexdigest(),g['module']
large=[str(p.relative_to(E)) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000];assert not large,large
scopes=len(rows);assert scopes<=200
summary=dict(authorization='Resume modules12–13,200 scopes,0 Kani,0 extraction',scopes_used=scopes,scope_budget=200,scopes_remaining=200-scopes,kani=0,extraction=0,successful=sum(r['exit_status']==0 for r in rows),failed=sum(r['exit_status']!=0 for r in rows),wall_seconds=sum(r['wall_seconds']for r in rows),peak_rss_kib=max(int(r['peak_rss_kib'])for r in rows),swaps=0,raw_roots=len(coverage),standard_only=True,full_functional='NOT PROVED',target_established=False,row_credit_claimed=False,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),scopes=[{k:r[k]for k in ['attempt','kind','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes']}for r in rows])
(E/'LIBB_RESUME_VALIDATION.json').write_text(json.dumps(summary,indent=1)+'\n')
(E/'LIBB_RESUME_AUDIT_COVERAGE.json').write_text(json.dumps(coverage,indent=1)+'\n')
(E/'LIBB_RESUME_TRANSCRIPT.tsv').write_text('attempt\tkind\ttarget\texit\twall_s\tpeak_RSS_KiB\tswap\n'+''.join('\t'.join(str(r[k])for k in ['attempt','kind','module','exit_status','wall_seconds','peak_rss_kib','swaps'])+'\n' for r in rows))
print(json.dumps({k:v for k,v in summary.items()if k!='scopes'}))
