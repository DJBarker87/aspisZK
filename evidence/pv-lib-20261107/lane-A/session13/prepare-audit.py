"""Build the own-root manifest; reuse the unchanged strict driver body."""
from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).parent
accepted={}
for p in sorted(E.glob('receipt-*.json')):
    r=json.loads(p.read_text())
    if r['accepted'] and not r['runtime_audit'] and 'RawAudit' not in r['target'] and r['target'] != 'PV_LIB_A_Reaudit12S13':
        accepted[r['target']]=r
support=[];roots=[]
for module,r in accepted.items():
    p=Path('lean',module+'.lean');source=p.read_text()
    assert hashlib.sha256(source.encode()).hexdigest()==r['source_sha256']
    namespace=re.search(r'^namespace (\S+)',source,re.M)[1]
    own=[namespace+'.'+n for n in re.findall(r'^#print axioms (\S+)',source,re.M)]
    assert own
    roots.extend(own)
    support.append(dict(module=module,source=str(p),source_sha256=r['source_sha256'],
      attempt=r['attempt'],roots=own,qualification='PARTIAL: see MODEL_FINDINGS.md; no full loop/callee invariant, callback linkage, f361-through14756 or joint witness'))
assert len(roots)==len(set(roots))
template=Path('lean/PV_LIB_A_Reaudit12S13.lean').read_text()
a=template.index('  let (modules, roots) :=');b=template.index('  let env ←',a)
arrays='  let (modules, roots) :=\n    (#['+', '.join('`'+m for m in accepted)+'],\n     #['+', '.join('`'+r for r in roots)+'])\n'
source=template[:a]+arrays+template[b:]
Path('lean/PV_LIB_A_RawAudit13.lean').write_text(source)
assert source[:a]==template[:a] and source[source.index('  let env ←'):]==template[b:]
(E/'SUPPORT.json').write_text(json.dumps(support,indent=2)+'\n')
(E/'AUDIT_ROOTS.json').write_text(json.dumps(dict(modules=list(accepted),roots=roots,
    driver='PV_LIB_A_RawAudit13',template='PV_LIB_A_Reaudit12S13',
    unchanged_except_module_and_root_arrays=True),indent=2)+'\n')
print(len(accepted),'modules;',len(roots),'own roots')
