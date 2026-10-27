from pathlib import Path
import json,re,subprocess,hashlib,collections
P=Path(__file__).resolve().parent;root=P.parents[2]
def load(n):return json.loads((P/n).read_text())
rows=load('rows3.json');old=json.loads((P.parent/'recount2/rows2.json').read_text());by={r['id']:r for r in rows};pins=load('pins.json')
assert len(rows)==len(by)==407
for a,b in zip(old,rows):
 for field in ['id','name','meaning','classification','definition']:
  assert a.get(field)==b.get(field),(a['id'],field)
ledger=(root/'design/PRIVACY-LEDGER-20261026.md').read_bytes();original=subprocess.check_output(['git','show',pins['research']+':design/PRIVACY-LEDGER-20261026.md'])
assert ledger.startswith(original)
assert ledger.count(b'## Recount 3 2026-10-27 (B)')==1
assert sum(r['recount3_status']=='OPEN' for r in rows)==103
assert collections.Counter(r['dependency_bucket'] for r in rows if r['recount3_status']=='OPEN')=={'a':44,'b':51,'c':8}
assert collections.Counter(r['recount3_status'] for r in rows)=={'OPEN':103,'REDUCED':176,'EVIDENCED':14,'CLOSED-ON-RESEARCH':87,'CLOSED-ON-CANDIDATE':27}
assert collections.Counter(r['classification'] for r in rows)=={'T':26,'P':376,'C':5}
closed=[r for r in rows if r['recount3_status']=='CLOSED-ON-CANDIDATE'];assert collections.Counter(r['in_headline_closure'] for r in closed)=={'candidate':17,'neither':10}
assert sum(r.get('closure_theorem') is not None for r in closed)==26
assert collections.Counter(r['in_headline_closure'] for r in rows)=={'research':160,'candidate':133,'neither':114}
assert by['V195']['recount3_status']=='OPEN';assert by['V163']['dependency_bucket']=='b';assert by['V240']['dependency_bucket']=='a'
assert sum(re.match(r'op229\b',r['name']) is not None for r in rows)==1
receipts=load('receipts.json');assert len(receipts)==20
assert [x['attempt'] for x in receipts]==list(range(38600,38620))
assert collections.Counter(x['exit'] for x in receipts)=={'0':19,'1':1}
for x in receipts:
 assert x['compiler_invoked'] and x['wall'] and x['peak_RSS_KiB'] and x['swap']=='0' and x['source_revision']
 assert x['limits']==dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,Lean_M=7000)
 assert not any('sorryAx' in l for l in x['axioms'])
 raw=(P/x['log']).read_text()
 for a in re.findall(r'depends on axioms:\s*\[([^]]*)\]',raw):
  assert set(a.replace('\n',' ').replace(' ','').split(',')) <= {'propext','Classical.choice','Quot.sound'},(x['attempt'],a)
for c in load('checks.json'):
 data=(P/c['source']).read_bytes();assert hashlib.sha256(data).hexdigest()==c['sha256']
 for l in data.decode().splitlines():assert l.startswith(('import ','set_option pp.explicit ','#check ','#print ')),l
for c in load('import-closures.json'):assert not c['unresolved_project_modules'],c['root']
retained=0
for m in load('manifest.json'):
 f=P/m['snapshot']
 if m.get('retained_snapshot'):
  assert f.is_file(),str(f);assert hashlib.sha256(f.read_bytes()).hexdigest()==m['sha256'],str(f);retained+=1
 else:assert not f.exists(),str(f)
assert retained==98,retained
assert sum(x['same_as_recount2'] for x in load('definition-audit3.json'))==374
# Only authorized paths may differ from the pinned research base.
paths=subprocess.check_output(['git','diff','--name-only',pins['research']]).decode().splitlines()
assert all(p=='design/PRIVACY-LEDGER-20261026.md' or p.startswith('evidence/privacy-recount-20261026/') for p in paths),paths
result=dict(rows=407,original_rows_preserved=403,ledger_original_prefix_preserved=True,lean_invocations=20,lean_pass=19,lean_diagnostic_failure=1,kani_invocations=0,axioms='accepted reports standard only',source_equation_rows=26,candidate_closure_imports=dict(research=0,candidate=17,neither=10),retained_text_snapshots=retained,open_buckets=dict(a=44,b=51,c=8),target_established=False)
(P/'validation3.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
