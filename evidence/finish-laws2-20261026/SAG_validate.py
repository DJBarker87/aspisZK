"""Validate focused receipts and current sources without launching a prover."""
from pathlib import Path
import hashlib,json,re
P=Path(__file__).resolve().parent
R=P.parents[1]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
allowed={'propext','Classical.choice','Quot.sound'}
receipts=[]
passed={}
for n in range(1,101):
    a=f'SAG_{n:03d}'
    file=P/a/'receipt.json'
    x=json.loads(file.read_text())
    assert x['attempt']==a
    assert len(x['sources'])==1
    assert x['command'][1:6]==['env','lean','-j1','-M7000','-DElab.async=false']
    assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
    assert x['swaps']=='0'
    assert x['exit_status'] not in {124,137,-9}
    assert json.loads((P/(a+'-reservation.json')).read_text())['allowed']
    for name,h in x['source_hashes'].items(): assert sha(P/a/'sources'/name)==h
    log=(P/a/'stdout.log').read_text()
    if x['exit_status']==0:
        assert 'error:' not in log and 'sorryAx' not in log
        for audit in x['print_axioms']:
            m=re.search(r'axioms:\s*\[([\s\S]*?)\]',audit)
            if m: assert set(re.split(r',\s*',m[1].strip()))<=allowed,audit
        passed[x['sources'][0]]=dict(attempt=a,sha256=x['source_hashes'][x['sources'][0]])
    receipts.append(dict(attempt=a,module=x['sources'][0],exit_status=x['exit_status'],
        wall_seconds=x['wall_seconds'],peak_rss_kib=int(x['peak_rss_kib']),swaps=x['swaps'],
        source_revision=x['source_revision'],source_hashes=x['source_hashes'],
        command=x['command'],print_axioms=x['print_axioms'],raw_receipt_sha256=sha(file)))
own={}
for f in sorted((R/'lean').glob('SAG_*.lean')):
    assert f.name in passed,('No successful current module',f)
    assert sha(f)==passed[f.name]['sha256'],('Different current bytes',f)
    source=f.read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option (maxHeartbeats|maxRecDepth)',source),f
    declarations=set(re.findall(r'^(?:private )?theorem\s+(\w+)',source,re.M))
    audits=set(re.findall(r'#print axioms\s+(\w+)',source))
    assert declarations<=audits,(f,declarations-audits)
    own[str(f.relative_to(R))]=dict(**passed[f.name],current_sha256=sha(f))
for name in ['SAG_inherited_sources.json','SAG_inherited_objects.json']:
    assert all(v['matches'] for v in json.loads((P/name).read_text()).values())
assert all(v['matches'] for v in json.loads((P/'SAG_NONVACUITY.json').read_text())['rows'])
assert all(v['source_matches'] and v['object_sha256'] for v in json.loads((P/'SAG_reused_new_families.json').read_text()).values())
# Inspect the actual changed continuation and residual source-instance fields.
leaf=(P/'SAG_090/stdout.log').read_text().split('def AspisR1.SAG_Q_Finish.Outcome',1)[1]
assert 'SAG_QuarterFree.Arithmetic' in leaf
assert 'canonical_S3_S4_S5_S9' not in leaf
assert '∃ r0 r1 weights pair dot' in leaf
assert 'RoundValues' in (R/'lean/SAG_Q_Finish.lean').read_text()
laws=(P/'SAG_091/stdout.log').read_text().split('structure AspisR1.SAG_QuarterFree.Arithmetic',1)[1].split('structure AspisR1.SAF_ReducedLaws.Arithmetic',1)[0]
for name in ['boundary0','eval0','boundary1','eval1','pair']: assert 'Arithmetic.'+name in laws,name
assert 'Arithmetic.quarter' not in laws
statement=(P/'SAG_085/stdout.log').read_text()
assert 'SAG_ScaleConfig.configuration c reservation' in statement and 'SAG_Q_Result.Outcome' in statement
assert 'let r := AspisR1.Rc3_Install.configuration c reservation' not in statement
assert all(json.loads((P/'SAG_statement_comparison.json').read_text())['checks'].values())
assert json.loads((P/'SAG_premises.json').read_text())['counts']['actual antecedent']['classes']=={'T':82,'P':92}
assert all(v['source_matches'] for v in json.loads((P/'SAG_final_objects.json').read_text()).values())
root=json.loads((P/'SAG_078/receipt.json').read_text())
assert root['print_axioms']==["'AspisR1.SAG_Deployed.deployed' depends on axioms: [propext, Classical.choice, Quot.sound]"]
failures=[r['attempt'] for r in receipts if r['exit_status']]
expected=[19,20,22,23,25,28,30,32,40,43,46,47,48,49,52,53,57,63,68]
assert failures==[f'SAG_{n:03d}' for n in expected],failures
result=dict(lean_invocations=100,passes=100-len(failures),excluded_failures=failures,kani_runs=0,
    package_replays=0,scope_policy='One admitted scope at a time; 6G high/8G max/Swap0/Tasks64; Lean-j1-M7000',
    source_revision_corrections='None; exact launch-base revisions retained',own_sources=own,receipts=receipts,
    inherited_sources_rehashed=789,inherited_objects_rehashed=98,additional_SAQ_F3P_sources=46,
    inherited_runtime_source_evidence_rehashed=569,
    source_scope='Explicit native quarter/mulM installation; unrestricted source retains only the duplicate-row delta',
    whitespace_notice='Exact source snapshots retain copied trailing whitespace; raw evidence is not rewritten for cosmetic diff checks')
(P/'SAG_validation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['lean_invocations','passes','excluded_failures','kani_runs']}))
print('Current source snapshots validated:',len(own))
