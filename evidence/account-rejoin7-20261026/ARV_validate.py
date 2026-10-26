"""Offline receipt, scope, statement, axiom and atomic-ledger validation."""
from pathlib import Path
from collections import Counter
import hashlib,json,re,subprocess,sys
P=Path(__file__).resolve().parent; R=P.parents[1]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
expected_limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
records=[]; accepted={}; errors=[]
def check(ok,description):
    if not ok:errors.append(description)
for path in sorted(P.glob('ARV_*/receipt.json')):
    x=json.loads(path.read_text()); records.append(x)
    check(x['limits']==expected_limits,str(path)+': caps')
    check(x['swaps']=='0',str(path)+': swap')
    check('-M7000' in x['command'] and '-j1' in x['command'],str(path)+': Lean flags')
    check(bool(x.get('source_revision')),str(path)+': revision')
    check(bool(x['deps_fingerprint'].get('lean_binary_sha256')),str(path)+': Lean binary fingerprint')
    for name,digest in x['source_hashes'].items():
        check(sha(path.parent/'sources'/name)==digest,str(path)+': source snapshot')
        if x['exit_status']==0:accepted.setdefault(name,[]).append((digest,x['attempt']))
    if x['exit_status']==0:
        for line in x['print_axioms']:
            check('sorryAx' not in line,str(path)+': rejected axiom in accepted output')
            m=re.search(r'\[([^]]*)\]',line,re.S)
            if m:check(set(t.strip() for t in m[1].split(',') if t.strip()) <= {'propext','Classical.choice','Quot.sound'},str(path)+': nonstandard axioms')
check(len(records)<=100,'Lean budget exceeded')
if '--final' in sys.argv:check(len(records)==100,'Whole 100-invocation budget not used')
modules={}; theorem_names=[]
for f in sorted((R/'lean').glob('ARV_*.lean')):
    check(any(d==sha(f) for d,_ in accepted.get(f.name,[])),str(f)+': no exact-source passing receipt')
    s=f.read_text(); modules[f.name]=sha(f)
    check(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\b|set_option\s+(maxHeartbeats|maxRecDepth)',s,re.M),str(f)+': prohibited proof token')
    ns=re.search(r'^namespace (\S+)',s,re.M)
    if ns:
        for n in re.findall(r'^theorem (\w+)',s,re.M):
            full=ns.group(1)+'.'+n; theorem_names.append(full)
            check('#print axioms '+n in s or '#print axioms '+full in s,str(f)+': missing own theorem audit '+n)
ledger=json.loads((P/'ARV_LEDGER_DELTA.json').read_text())
counts={}
for scope in ['actual antecedent','deployment only','deployment alias']:
    c=Counter(row['classification'] for row in ledger['rows'] if row['scope']==scope)
    counts[scope]={'rows':sum(c.values()),'classes':{k:c[k] for k in 'TPGC'}}
c=Counter(counts['actual antecedent']['classes']); c.update(counts['deployment only']['classes'])
counts['deduplicated actual plus non-alias deployment']={'rows':sum(c.values()),'classes':dict(c)}
check(counts==ledger['before']==ledger['after'],'fresh atomic recount differs')
check(ledger['delta']==dict.fromkeys('TPGC',0),'actual-root delta')
check(ledger['removed']==ledger['added']==ledger['reclassified']==[],'actual-root rows altered')
check(ledger['source_before_sha256']==ledger['source_after_sha256']==sha(R/'lean/Rc10_Top.lean'),'actual root source changed')
check((P/'ARV_BEFORE_STATEMENT.lean.txt').read_bytes()==(P/'ARV_AFTER_ACTUAL_STATEMENT.lean.txt').read_bytes(),'actual before/after differ')
check(ledger['aliases']=={'L185':'L159'},'ledger alias changed')
check(sha(R/ledger['baseline_path'])==ledger['baseline_sha256'],'baseline ledger hash')
fixture=json.loads((P/'ARV_FIXTURE_PREDECESSORS.json').read_text())
for row in fixture['rows']:check(sha(R/row['path'])==row['sha256'],'fixture predecessor changed: '+row['path'])
base='6f05e91d0d8b96945b2d75386623beebc7971332'
changed=subprocess.check_output(['git','diff','--name-only',base],cwd=R,text=True).splitlines()
changed+=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=R,text=True).splitlines()
for name in changed:check(name.startswith('lean/ARV_') or name.startswith('evidence/account-rejoin7-20261026/'),'foreign scope: '+name)
check(not re.search(r'^theorem deployed\b',(R/'lean/ARV_Root.lean').read_text(),re.M),'unproved root renamed deployed')
summary=dict(status='PASS' if not errors else 'FAIL',errors=errors,lean_invocations=len(records),kani_runs=0,
    passing=sum(x['exit_status']==0 for x in records),excluded_failures=sum(x['exit_status']!=0 for x in records),
    wall_seconds=sum(float(x['wall_seconds']) for x in records),peak_rss_kib=max(int(x['peak_rss_kib']) for x in records),
    swaps=sum(int(x['swaps']) for x in records),module_count=len(modules),public_theorems=len(theorem_names),
    actual_root=ledger['actual_theorem'],removed=0,added=0,reclassified=0,actual_counts=counts,
    source_scope='only own ARV modules and evidence; no shipped/cfg(kani) edits',base=base,
    modules=modules,exact_source_accepted=accepted,theorems=theorem_names)
(P/'ARV_VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n')
(P/'ARV_attempts.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in records))
print(json.dumps({k:v for k,v in summary.items() if k not in ['modules','exact_source_accepted','theorems','actual_counts']},indent=2))
sys.exit(bool(errors))
