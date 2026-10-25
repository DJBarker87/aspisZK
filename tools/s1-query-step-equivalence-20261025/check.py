#!/usr/bin/env python3
"""Audit all disjoint native word-prefix partitions; no replay or whole-scan claim."""
from pathlib import Path
import json,hashlib,subprocess,re
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent
B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021'
P=E/'s1-query-step-history-v2';plan=json.loads((T/'plan-partition.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
j=json.loads((P/'collection.json').read_text())
for p,h in j['files'].items():assert sha(P/p)==h
src=E/'s1-query-step-equivalence-v2/source/query_step_equivalence_partition'
for p,h in plan['files'].items():assert sha(T/'binding-partition.json'if p=='query-binding.json'else src/p)==h
frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-core/src/r0_transcript.rs'],cwd=R,text=True)
wrapper=(T/'wrapper.rs').read_text();assert (src/'core-workspace/crates/aspis-core/src/r0_transcript.rs').read_text()==frozen+wrapper
start=frozen.index('            if self.accepted_len == QUERY_COUNT');end=frozen.index('\n        }\n        false',start)
assert frozen[start:end].replace('self.','scan.')in wrapper
proof=(T/'proofs.rs').read_text();assert proof==(src/'min/src/probe_block.rs').read_text()
assert 'kani::stub'not in proof and 'let n=N;'in proof and 'kani::assume(d<=64)'in proof
extracted=E/'s1-query-block-extraction-v1/v3/src/lib.rs'
def item(s,key):
 a=s.index(key);b=s.index('{',a)+1;d=1
 while d:d+=(s[b]=='{')-(s[b]=='}');b+=1
 return s[a:b]
for key in ['fn owned_contains(','fn owned_step(']:assert item(proof,key)==item(extracted.read_text(),key)
metrics=[];checks=0
for n in range(23):
 a=P/f'v4/run-{n}';r=json.loads((a/'verify-receipt.json').read_text());i=json.loads((a/'verify-input.json').read_text())
 assert r['exit_status']==0 and r['source_unchanged']and r['tools_unchanged']and r['swaps']==0
 assert i['source_pins']==plan['files']and i['command']==r['command']
 c=r['command'];assert c[c.index('--harness')+1]==f'proofs::word_value_equal_{n}'and c[c.index('--solver')+1]=='cadical'
 assert r['cgroup']['memory.max']==str(4*2**30)and r['cgroup']['memory.swap.max']=='0'
 assert all(re.search(r'^'+k+r' 0$',r['cgroup']['memory.events'],re.M)for k in ['high','max','oom','oom_kill'])
 o=(a/'verify-stdout.log').read_text();m=re.search(r'0 of (\d+) failed',o);assert m and 'VERIFICATION:- SUCCESSFUL'in o
 assert ('1 of 2 cover properties satisfied'if n==22 else '2 of 2 cover properties satisfied')in o
 checks+=int(m[1]);metrics.append(dict(prefix=n,wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib']))
print(json.dumps(dict(status='PASS',pins=len(j['files']),partitions=23,checks=checks,total_wall_seconds=sum(r['wall_seconds']for r in metrics),peak_rss_kib=max(r['peak_rss_kib']for r in metrics),swap=0,domain='accepted_len0..22,draws<=64,arbitrary22-wordbuffer andcandidateU32',qualification='Exact frozen single-word body splice; not actual native scan/iterator/driver/SDK closure. N22 stopped-only cover expected.',metrics=metrics)))
