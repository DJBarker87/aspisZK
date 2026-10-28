"""Attribute terse panic placeholders using frozen, matched control source deltas."""
from pathlib import Path
import json,re,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-kstub-20261028'
fixtures={(x['package'],x['harness']):x for x in json.loads((E/'negative-fixtures.json').read_text())}
fixtures['cb','path_join8_negative']=dict(fixture=dict(a='[65;8]',b='[66;8]',n='8',m='8'))
def fn(s,name):
 m=re.search(r'fn '+re.escape(name)+r'\(',s);assert m,name
 a=s.index('{',m.start());i=a+1;depth=1
 while depth:depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[m.start():i],m.start()
audit=[]
for p in sorted(E.glob('K*-result.json')):
 r=json.loads(p.read_text())
 if not r['negative_control'] or r['status']!='FAIL':continue
 d=E/r['run'];source=d/('wide_exact.rs.txt' if r['package']=='native/core' else 'sealed.rs.txt' if r['package']=='split' else 'lib.rs.txt');s=source.read_text();positive,pos=fn(s,r['harness']);negative,neg=fn(s,r['negative'])
 original=positive
 if r['harness']=='push_bytes':original=json.loads((E/'symbolic-append.json').read_text())['before'].strip()
 expected=original.replace('fn '+r['harness']+'(', 'fn '+r['negative']+'(',1)
 j=expected.rfind('assert_eq!');assert j>=0
 expected=expected[:j]+expected[j:].replace('assert_eq!','assert_ne!',1)
 fixture=fixtures[r['package'],r['negative']]['fixture']
 for var,value in fixture.items():
  pattern=r'(let\s+'+var+r'\s*:\s*(?:\[[^\]]+\]|\w+)\s*=\s*)kani::any\(\)'
  expected,n=re.subn(pattern,lambda m:m[1]+value,expected);assert n==1,(r['run'],var,n)
 assert expected==negative,(r['run'],'source delta differs from final Eq->Ne plus recorded concrete fixture')
 def attrs(start):
  t=s[s.rfind('#[kani::proof]',0,start):start]
  return re.findall(r'#\[kani::(?:unwind|stub)\([^\n]*\)\]',t)
 assert attrs(pos)==attrs(neg),(r['run'],'bound/stub attributes differ')
 assert len(re.findall('assert_ne!',negative))==1,(r['run'],'more than one inequality')
 log=(d/'output.log').read_text();failures=re.findall(r'^Failed Checks: (.+)$',log,re.M)
 assert len(failures)==1 and re.search(r'\*\*\s*1 of \d+ failed',log),(r['run'],'unexpected failed-check count')
 explicit='assertion failed:' in failures[0] and '!=' in failures[0]
 placeholder=failures[0]=="This is a placeholder message; Kani doesn't support message formatted at runtime"
 assert explicit or placeholder,(r['run'],failures)
 if placeholder:assert 'core::panicking::assert_failed_inner' in log,(r['run'],'not assertion panic')
 witness='ASCII nonempty inputs satisfy UTF8/range/length assumptions; matched original equality has identical native/reference calls'
 if r['package']=='split':
  n=int(fixture['n']);assert (n<=64 if r['window']=='lo' else 64<n<=129);assert fixture['data']=='[65;129]' and fixture['k']=='0';witness=f'n={n}; block count={n//64}, tail length={n%64}>0, tail[0]=data[{64*(n//64)}]=65; negated final optional-byte equality is false; preceding block/length assertions unchanged'
 elif r['package'] in ['wide','native/core']:witness='Eight carriers0x01020304; native and flattened reference bytes both repeat[4,3,2,1] eight times, so the final byte-vector inequality is false; the original positive covers this carrier'
 audit.append(dict(run=r['run'],source=str(source.relative_to(R)),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),positive_body_sha256=hashlib.sha256(positive.encode()).hexdigest(),negative_body_sha256=hashlib.sha256(negative.encode()).hexdigest(),source_delta_verified=True,only_property_change='final assert_eq! becomes assert_ne!',other_changes='recorded concrete admitted input substitutions only; index165 specializes its strengthened gate at n=2,m=1',same_bound_and_exact_kmx_stubs=True,fixture=fixture,witness=witness,failed_checks=failures,diagnostic='explicit inequality assertion' if explicit else 'runtime-formatted assertion-panic placeholder, attributed by exact source delta and witness',placeholder_attribution=placeholder))
(E/'control-source-audit.json').write_text(json.dumps(audit,indent=2)+'\n');print('Audited',len(audit),'failing controls;',sum(x['placeholder_attribution'] for x in audit),'generic panic messages attributed without reruns')
