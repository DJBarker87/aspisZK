"""Read-only receipt/source/axioms audit; never invokes a prover or builder."""
from pathlib import Path
import hashlib,json,re,subprocess
root=Path(__file__).resolve().parent
receipts=[]
for n in range(1,101):
    p=root/f'Hiq_{n:03}'/'receipt.json'
    if p.exists():
        row=json.loads(p.read_text()); assert row['attempt']==f'Hiq_{n:03}'
        assert row['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
        receipts.append(row)
    else:
        assert n==22, n
        assert (root/'Hiq_022-prelaunch.json').exists()
passed=[r for r in receipts if r['exit_status']==0]
current={}
for p in sorted(Path('lean').glob('Hiq_*.lean')):
    digest=hashlib.sha256(p.read_bytes()).hexdigest()
    matches=[r for r in passed if r['source_hashes'].get(p.name)==digest]
    assert matches, str(p)
    r=matches[-1]
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option (maxRecDepth|maxHeartbeats)',p.read_text()), str(p)
    theorems=re.findall(r'^theorem\s+([A-Za-z0-9_]+)',p.read_text(),re.M)
    for theorem in theorems:
        assert f'#print axioms {theorem}' in p.read_text(), (p,theorem)
    for line in r['print_axioms']:
        assert 'sorryAx' not in line and all(x.strip() in {'propext','Classical.choice','Quot.sound'} for x in re.search(r'\[([^]]*)\]',line).group(1).split(',')) if '[' in line else True
    current[str(p)]={'sha256':digest,'passing_attempt':r['attempt'],'axioms':r['print_axioms']}
result={'charged_submissions':100,'actual_invocations':len(receipts),'prelaunch_failures':1,'passing_invocations':len(passed),'failed_invocations':len(receipts)-len(passed),'kani_runs':0,'modules':current,'cumulative_wall_seconds':sum(r['wall_seconds'] for r in receipts),'largest_peak_rss_kib':max(int(r['peak_rss_kib']) for r in receipts),'swaps':sorted(set(r['swaps'] for r in receipts)),'excluded':'All failed outputs, including recovery sorryAx; AccountTransport was not delivered','final_audit':next(r for r in receipts if r['attempt']=='Hiq_100')}
(root/'Hiq_validation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in {'modules','final_audit'}},indent=2))
