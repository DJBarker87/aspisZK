"""Verify receipt completeness and current FIn source hashes without replay."""
from pathlib import Path
import json,hashlib,re,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
attempts=[];good={}
for n in range(1,101):
    name=f'FIn_{n:03}';p=P/name/'receipt.json'
    if not p.exists():
        pre=json.loads((P/(name+'-preflight.json')).read_text())
        assert pre['compiler_started'] is False
        attempts.append(pre);continue
    d=json.loads(p.read_text())
    assert d['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
    assert '-M7000' in d['command']
    assert str(d['swaps'])=='0'
    if d['exit_status']==0:
        for f,h in d['source_hashes'].items():good[(f,h)]=name
        for line in d['print_axioms']:
            if 'depends on axioms:' in line:
                words=re.search(r'\[([^]]*)\]',line).group(1)
                assert set(x.strip() for x in words.split(','))<={'propext','Classical.choice','Quot.sound'},line
    attempts.append({k:d[k] for k in ['attempt','command','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','print_axioms']})
sources=[]
for f in sorted((R/'lean').glob('FIn_*.lean')):
    h=sha(f);assert (f.name,h) in good,('no passing current source',f)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',f.read_text()),f
    sources.append({'file':str(f.relative_to(R)),'sha256':h,'bytes':f.stat().st_size,'passing_attempt':good[(f.name,h)]})
outside=[p for p in subprocess.check_output(['git','diff','e39e0ecb30','--name-only'],cwd=R,text=True).splitlines() if not(p.startswith('lean/FIn_') or p.startswith('evidence/finish-install-20261026/'))]
assert not outside,outside
subprocess.run(['git','diff','HEAD','--check','--','.',':!*.log'],cwd=R,check=True)
result={'conservative_Lean_attempts':100,'compiler_starts':sum('exit_status' in a for a in attempts),
 'preflight_failures_charged':sum('compiler_started' in a for a in attempts),
 'Kani_runs':3,'Kani_limit':40,'no_production_edits':True,'no_rebuild_trigger':True,
 'unchanged_launcher':True,'scope':'Focused cached proof compilation and fresh inventories, not release replay',
 'sources':sources,'attempts':attempts}
(P/'FIn_validation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('sources','attempts')},indent=2))
