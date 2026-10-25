#!/usr/bin/env python3
"""Read-only solver/source identity audit for exact helper result equality."""
from pathlib import Path
import json,hashlib,re,subprocess
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent;B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';P=E/'s1-sampler-value-history-v1'
j=json.loads((P/'collection.json').read_text());plan=json.loads((T/'plan.json').read_text())
for p,h in j['files'].items():assert hashlib.sha256((P/p).read_bytes()).hexdigest()==h
A=P/'v2/run-value';r=json.loads((A/'verify-receipt.json').read_text());i=json.loads((A/'verify-input.json').read_text())
assert r['exit_status']==0 and r['source_unchanged']and r['tools_unchanged']and r['swaps']==0
assert i['source_pins']==plan['files'] and i['command']==r['command']
assert r['command'][r['command'].index('--solver')+1]=='z3'and any(k.endswith('/z3-tool-v1/bin/z3')for k in i['tool_pins'])
assert json.loads((A/'compile-reuse.json').read_text())['compiler_replayed']==False
assert r['cgroup']['memory.max']==str(12*2**30)and r['cgroup']['memory.swap.max']=='0'
assert all(re.search(r'^'+k+r' 0$',r['cgroup']['memory.events'],re.M)for k in ['high','max','oom','oom_kill'])
o=(A/'verify-stdout.log').read_text();assert '0 of 320 failed'in o and '1 of 1 cover properties satisfied'in o and 'VERIFICATION:- SUCCESSFUL'in o
actual=(T/'value_sampler.rs').read_text();assert 'kani::stub'not in actual and 'kani::assume'not in actual
src=E/'s1-sampler-value-equivalence-v2/source/sampler_value_equivalence/min/src/value_sampler.rs';assert src.read_text()==actual
frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-r1-cost-probe/src/sampler.rs'],cwd=R,text=True);assert actual.startswith(frozen+'\n#[cfg(kani)]')
bad=P/'v1/run-value';q=json.loads((bad/'verify-receipt.json').read_text());assert q['exit_status']==1 and 'CBMC timed out'in(bad/'verify-stdout.log').read_text()
assert i['source_pins']==json.loads((bad/'verify-input.json').read_text())['source_pins']
print(json.dumps(dict(status='PASS',pins=len(j['files']),complete8_digits_and_quotient_equal=True,domain='all32-byte blocks',result_stubs=0,solver_only_change=True,wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swap=0,wholeSDK_oracle_release_not_closed=True)))
