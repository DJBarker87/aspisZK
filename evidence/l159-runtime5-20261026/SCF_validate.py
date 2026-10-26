"""Offline source, focused receipt, axiom and unchanged-root ledger validation."""
from pathlib import Path
from collections import Counter
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent; R=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text())
base=load(E/'SCF_BASELINE.json'); root=R/'lean/Rc7_Top.lean'
assert sha(root)==base['files']['lean/Rc7_Top.lean']
assert root.read_bytes()==(E/'SCF_BEFORE.lean.txt').read_bytes()
assert (E/'SCF_HOST_ROOT_SHA256.txt').read_text().split()[0]==sha(root)
records=[]; passed={}; standard={'propext','Classical.choice','Quot.sound'}
for p in sorted(E.glob('SCF_[0-9][0-9][0-9]/receipt.json')):
    d=load(p);records.append(d)
    assert d['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
    assert int(d['swaps'])==0
    for f,h in d['source_hashes'].items():assert sha(p.parent/'sources'/f)==h
    if d['exit_status']!=0:continue
    assert 'error:' not in (p.parent/'stdout.log').read_text()
    for line in d['print_axioms']:
        assert 'sorryAx' not in line
        found=re.search(r'depends on axioms: \[([^\]]*)\]',line)
        if found: assert set(map(str.strip,found[1].split(','))) <= standard
    for f,h in d['source_hashes'].items():
        if (R/'lean'/f).exists() and sha(R/'lean'/f)==h:passed[f]=d['attempt']
modules=sorted((R/'lean').glob('SCF_*.lean'))
host=load(E/'SCF_HOST_MANIFEST.json')
for name,items in host.items():
    if name.endswith('.lean'):
        source=next(v for k,v in items.items() if k.endswith('/'+name))
        assert source['sha256']==sha(R/'lean'/name),name
for p in modules:
    assert p.name in passed,p.name
    s=p.read_text()
    assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s|set_option\s+(maxHeartbeats|maxRecDepth)',s,re.M),p
for p in R.glob('lean/SCF_*.olean'):raise AssertionError(p)
assert len(records)<=100
# Re-enumerate the atomic ledger, retaining all guards/witnesses/family rows.
old=load(R/'evidence/rejected-prefix-20261026/RPx_premises.json')
rows=old['rows'];counts={}
for scope in ['actual antecedent','deployment only','deployment alias']:
    c=Counter(r['classification'] for r in rows if r['scope']==scope)
    counts[scope]={k:c[k] for k in 'TPGC'}
    assert counts[scope]==old['counts'][scope]
for name, selected in [('deduplicated actual plus non-alias deployment',[r for r in rows if r['scope']!='deployment alias']),('all audit rows',rows)]:
    c=Counter(r['classification'] for r in selected);counts[name]={k:c[k] for k in 'TPGC'}
ledger=dict(actual_theorem='AspisR1.Rc7_Top.deployed',new_deployed_endpoint=None,
 method=old['method'],classification_citation=old['classification_citation'],rows=rows,
 counts=counts,removed_rows=[],added_rows=[],reclassified_rows=[],
 delta={scope:{k:0 for k in 'TPGC'} for scope in counts},
 evidence='Exact unchanged source; fresh SCF_019 kernel statement/axioms; inherited RPx expanded family inventories, no fresh field expansion.',
 inherited_field_catalog_sha256=sha(R/'evidence/rejected-prefix-20261026/RPx_field_catalog.json'),
 caveat='CleanAccountTransport is an UNPROVED named target. It is not installed as a retained premise; no SCF_Top.deployed exists.')
(E/'SCF_LEDGER_DELTA.json').write_text(json.dumps(ledger,indent=2)+'\n')
log=(E/'SCF_019/stdout.log').read_text();kernel=log.split("\n'AspisR1.",1)[0].rstrip()+'\n'
assert kernel.startswith('@AspisR1.Rc7_Top.deployed :')
for name in ['SCF_BEFORE_KERNEL.lean.txt','SCF_AFTER_KERNEL.lean.txt']:(E/name).write_text(kernel)
(E/'SCF_AFTER.lean.txt').write_bytes(root.read_bytes())
summary=dict(compiler_invocations=len(records),passes=sum(r['exit_status']==0 for r in records),
 failures=sum(r['exit_status']!=0 for r in records),precompiler_rejections=['SCF_004: missing SCF_Deletion.olean; no Lean started'],
 budget_max=100,Kani=0,dependency_builds=0,budget_exhausted=False,
 wall_seconds=sum(r['wall_seconds'] for r in records),peak_rss_kib=max(int(r['peak_rss_kib']) for r in records),swaps=0,
 current_modules={p.name:dict(sha256=sha(p),passing_attempt=passed[p.name]) for p in modules},
 current_deployed_root_sha256=sha(root),actual_premises_removed=0,
 stop='No proof of CleanAccountTransport on retained premises; do not adopt it as an extra source-refinement assumption.')
(E/'SCF_VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
