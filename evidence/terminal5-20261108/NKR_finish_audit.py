from pathlib import Path
import json,hashlib,collections
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rs=[json.loads(l)for l in(E/'NKR_ATTEMPTS.jsonl').read_text().splitlines()]
usage=collections.Counter(r['attempt'][4]for r in rs);assert usage=={'L':140,'K':70},usage
scopes=[]
for r in rs:
 a=r['attempt'];q=E/a/'receipt.json';s=json.loads(q.read_text());ad=json.loads((E/(a+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True,a
 assert s['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
 assert s['env']['CARGO_TARGET_DIR']=='/home/dombarker/project-offloads/codex-cx-terminal5-20261108/NKR_target',a
 assert s['exit_status']==r['exit_status'],a
 scopes.append(dict(attempt=a,target=s['module'],exit_status=s['exit_status'],wall_seconds=s['wall_seconds'],peak_rss_kib=s['peak_rss_kib'],swap=s['swaps'],cgroup_memory_peak_bytes=s.get('cgroup_memory_peak_bytes'),limits=s['limits'],source_revision=s['source_revision'],receipt_sha256=sha(q),print_axioms=s['print_axioms']))
classes=[json.loads(l)for l in(E/'NKR_RAW_CLASSIFICATIONS.jsonl').read_text().splitlines()];assert len(classes)==26 and all(c['accepted']for c in classes)
expected=json.loads((E/'NKR_AUDIT_ROOTS.json').read_text())['roots'];actual=[];dis=[]
for i in range(26):
 r=json.loads((E/f'NKR_audit/proof{i}/receipt.json').read_text());actual += [x['root']for x in r['results']];dis+=r['collect_axioms_disagreements']
assert len(actual)==len(set(actual))==len(expected)==10503 and set(actual)==set(expected)
fixtures=json.loads((E/'NKR_audit/fixtures/receipt.json').read_text());assert fixtures['fixture_pass']
obj=dict(status='INCOMPLETE_COMBINED_GATE_NO_LEDGER_CREDIT',target='TX1:256 NOT ESTABLISHED',headline='AspisR1.RPx_Deployed.deployed',baseline=dict(CLOSED=553,QUALIFIED=0,OPEN=46,total=599,authoritative_delta=0),candidate_rows=['TX1:225','TX1:232','TX1:251','TX1:250','TX1:220','TX1:218'],combined_import=dict(attempts=['NKR_L182','NKR_L184'],exit_status=[1,1],failure='explicit private helper source-name lookup; no third combined replay'),strict_scan=dict(status='NOT_RUN',reason='requires absent combined object; unchanged failed shape not launched'),raw_audit=dict(status='DIAGNOSTIC_PRIVATE_DIRECT_IMPORT_PASS',roots=len(actual),groups=26,standard_axioms=['propext','Classical.choice','Quot.sound'],collect_axioms_disagreements=dis,private_modules='NKR_AUDIT_MODULES.json',classifications_sha256=sha(E/'NKR_RAW_CLASSIFICATIONS.jsonl'),authority='ax2 raw walk; original exits and collector disagreements retained; no gate substitution'),fixtures=dict(exit_status=fixtures['exit_status'],pass_count=8),budget=dict(formal_support=usage['L'],native_support=usage['K'],extraction=0,limits=dict(L=140,K=70,E=0)),native=dict(pairs=26,inherited_pairs=44,release_validation='NKR_NATIVE_RELEASE.json',release_validation_sha256=sha(E/'NKR_NATIVE_RELEASE.json')),scopes=scopes,release_pins_sha256=sha(E/'NKR_RELEASE_PINS.json'),trust='P6/D188 optionA reclassification retained; no new runtime trust',review='NKR_ROOT_HYPOTHESES_REVIEW.md',root_statements='NKR_ROOT_STATEMENTS.md')
(E/'NKR_AUDIT.json').write_text(json.dumps(obj,indent=1)+'\n')
print(json.dumps({k:obj[k]for k in ['status','target','budget']}))
