"""Validate bq continuation receipts, source snapshots and raw own-root ax2."""
from pathlib import Path
import json,hashlib,lzma,re,subprocess
E=Path(__file__).resolve().parent
allrows=[json.loads(p.read_text())for p in sorted(E.glob('LIBB_L[0-9][0-9][0-9]/receipt.json')) if 301<=int(p.parent.name[-3:])<=500]
rows=[r for r in allrows if int(r['attempt'][-3:])>=325]
assert len(allrows)<=200
attempts=[json.loads(l)for l in (E/'LIBB_ATTEMPTS.jsonl').read_text().splitlines()]
for r in rows:
 a=r['attempt'];d=E/a
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
 ad=json.loads((E/(a+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True,a
 assert int(r['swaps'])==0
 disk=sorted(E.glob(a+'-disk-*.json'))[-1];assert json.loads(disk.read_text())['free']>=40_000_000_000
 shares=[x for x in attempts if x.get('attempt')==a and x.get('event')=='share_check'];assert shares[-1]['host']['count']<6
 for n,h in r['source_hashes'].items():assert hashlib.sha256((d/'sources'/n).read_bytes()).hexdigest()==h
 assert r['source_revision']
 if r['exit_status']==0:assert 'sorryAx' not in (d/'stdout.log').read_text()
coverage=[];standard={'propext','Classical.choice','Quot.sound'}
for g in json.loads((E/'LIBB_GATE_AUDITS.json').read_text()):
 s=(E/(g['module']+'.lean')).read_text();assert hashlib.sha256(s.encode()).hexdigest()==g['source_sha256']
 assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b',s)
 good=[r for r in rows if r['kind']=='lean' and r['module']==g['module'] and r['exit_status']==0]
 assert good and g['source_sha256'] in good[-1]['source_hashes'].values()
 audit=json.loads((E/'LIBB_audit'/g['mode']/(g['mode']+'.json')).read_text());assert audit['exit_status']==0
 assert {x['root']for x in audit['results']}==set(g['roots'])
 for x in audit['results']:
  assert x['equal'] is True and set(x['collect_axioms'])==set(x['walked_axioms'])<=standard
  n='LIBB_NEP_'+g['mode']+'_'+x['root']+'_REACHABLE.txt'
  raw=lzma.decompress((E/(n+'.xz')).read_bytes());assert hashlib.sha256(raw).hexdigest()==(E/(n+'.sha256')).read_text().strip()
  coverage.append(dict(module=g['module'],root=x['root'],raw=n+'.xz',axioms=x['walked_axioms'],equal=True))
assert len(coverage)==18
assert any(r['module']=='LIBB_GATE_IMPORT' and r['exit_status']==0 for r in rows)
assert not [p for p in E.rglob('*')if p.is_file()and p.stat().st_size>20_000_000]
keys=['attempt','kind','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes']
summary=dict(authorization='Same module12/13 resume:200 scopes,L301-L500;0 Kani;0 extraction',scopes_total=len(allrows),scopes_this_continuation=len(rows),remaining=200-len(allrows),successful=sum(r['exit_status']==0 for r in rows),excluded=sum(r['exit_status']!=0 for r in rows),wall_seconds=sum(r['wall_seconds']for r in rows),peak_rss_kib=max(int(r['peak_rss_kib'])for r in rows),successful_peak_rss_kib=max(int(r['peak_rss_kib'])for r in rows if r['exit_status']==0),swap=0,raw_roots=len(coverage),standard_only=True,gate='ReturnFunctional: entire returned Obs including events',modules12_13='DONE under bq clarification',strict_whole_observation_functional='not required; not claimed',I_f064='integration-owned',ledger_credit_claimed=False,security_target_established=False,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),scopes=[{k:r[k]for k in keys}for r in rows])
(E/'LIBB_GATE_VALIDATION.json').write_text(json.dumps(summary,indent=1)+'\n')
(E/'LIBB_GATE_AUDIT_COVERAGE.json').write_text(json.dumps(coverage,indent=1)+'\n')
(E/'LIBB_GATE_TRANSCRIPT.tsv').write_text('attempt\tkind\ttarget\texit\twall_s\tpeak_RSS_KiB\tswap\n'+''.join('\t'.join(str(r[k])for k in keys[:7])+'\n'for r in rows))
print(json.dumps({k:v for k,v in summary.items()if k!='scopes'}))
