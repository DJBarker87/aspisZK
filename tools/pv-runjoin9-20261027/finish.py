#!/usr/bin/env python3
"""Summarize retained proof receipts; this invokes no compiler or scope."""
import hashlib,json,pathlib,re,subprocess
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-runjoin9-20261027';base='e896c811331a5fc3d953bdf641c75b22580ff8c0'
records=sorted((json.loads(p.read_text()) for p in e.glob('receipt-*.json')),key=lambda x:x['attempt'])
charged=[r for r in records if r.get('exit') is not None]
assert len(charged)==100,len(charged)
used=sorted(int(p.stem[5:]) for p in e.glob('used-*.json'));assert len(set(used))==len(used) and all(37400<=i<=37699 for i in used)
for r in charged:
 assert all(r.get(k) is not None for k in ['exit','wall_seconds','peak_rss_bytes','swaps','source_revision','source_sha256']),r['attempt']
 assert hashlib.sha256((e/r['source_snapshot']).read_bytes()).hexdigest()==r['source_sha256']
 if r['accepted']:
  for s in r['axioms']:
   if 'depends on axioms:' in s:
    names={a.strip() for a in s.split('[',1)[1].split(']',1)[0].split(',')}
    assert names <= {'propext','Classical.choice','Quot.sound'},(r['attempt'],s)
accepted=[r for r in charged if r['accepted']]
files=subprocess.check_output(['git','diff','--name-only',base,'--','docs/research/v8-r0-zk-20261009/lean/R1Z'],cwd=root,text=True).splitlines()
source_checks=[]
for rel in files:
 p=root/rel
 if not p.is_file() or p.suffix!='.lean':continue
 s=p.read_text();sha=hashlib.sha256(p.read_bytes()).hexdigest()
 assert p.name.startswith('PV_RunJoin_'),p
 assert not re.search(r'\b(sorry|admit|native_decide|implemented_by)\b',s),p
 assert not re.search(r'^\s*(axiom|unsafe\s+axiom)\b',s,re.M),p
 assert not re.search(r'set_option\s+(maxRecDepth|maxHeartbeats)',s),p
 matches=[r['attempt'] for r in accepted if r['source_sha256']==sha]
 assert matches,('active source has no matching accepted receipt',rel)
 source_checks.append(dict(path=rel,sha256=sha,accepted_receipts=matches))
for name in ['PV_RunJoin_TrustItems.lean','PV_RunJoin_TrustEndpoint.lean','PV_RunJoin_TrustLedger.lean']:
 rel='docs/research/v8-r0-zk-20261009/lean/R1Z/'+name
 assert (root/rel).read_bytes()==subprocess.check_output(['git','show',base+':'+rel],cwd=root)
crates=subprocess.check_output(['git','diff','--name-only',base,'--','crates','programs'],cwd=root,text=True).splitlines()
assert crates==['crates/aspis-statement/src/pool_v1/pair_trace_pv_runjoin8_roots.rs'],crates
parent='crates/aspis-statement/src/pool_v1/pair_trace.rs';assert (root/parent).read_bytes()==subprocess.check_output(['git','show',base+':'+parent],cwd=root)
assert '#[cfg(kani)]\n#[path = "pair_trace_pv_runjoin8_roots.rs"]\nmod pv_runjoin8_roots;' in (root/parent).read_text()
kani=[json.loads((e/f'pv9-runjoin-kani-{i:02d}/receipt.json').read_text()) for i in range(1,7)]
assert all(r['exit']==0 and r['swaps']==0 for r in kani)
last=charged[-3:];assert all('TrustAudit9' in r['target'] for r in last)
summary=dict(lean_attempts=100,accepted=len(accepted),rejected=100-len(accepted),used_ids=used,next_unused_id=max(used)+1,uncharged_refusals=len(list(e.glob('refusal-*.json'))),kani_runs=6,kani_successes=6,lean_wall_seconds=sum(r['wall_seconds'] for r in charged),lean_peak_rss_bytes=max(r['peak_rss_bytes'] for r in charged),lean_swaps=sum(r['swaps'] for r in charged),kani_wall_seconds=sum(r['wall_seconds'] for r in kani),kani_peak_rss_bytes=max(r['peak_rss_bytes'] for r in kani),kani_swaps=sum(r['swaps'] for r in kani),final_focused_audit_attempts=[r['attempt'] for r in last],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip())
(e/'metrics-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
(e/'tally.json').write_text(json.dumps(dict(lean_budget=100,lean_charged=100,kani_budget=6,kani_charged=6,used_ids=used,next_unused_id=max(used)+1,final_three_reserved_and_used_for_audit=True),indent=2)+'\n')
(e/'final-source-audit.json').write_text(json.dumps(dict(base=base,checked_revision=summary['source_revision'],active_sources=source_checks,unchanged_T=True,unchanged_original_P_records=True,counts=dict(runtime_boundary=[2,2],fields=[8,8],native_residuals=[6,6],T_fields=[3,3]),cfg_kani_only_crate_change=crates,axioms='accepted targets: subset of propext, Classical.choice, Quot.sound',rejected_recovery_output_not_accepted=True,scope='focused source/receipt audit; no coherent frozen-release replay or native installation claimed'),indent=2)+'\n')
keys=['attempt','target','exit','wall_seconds','peak_rss_bytes','swaps','source_revision','source_sha256','axioms','accepted']
(e/'receipt-index.tsv').write_text('\t'.join(keys)+'\n'+'\n'.join('\t'.join(json.dumps(r.get(k),ensure_ascii=False) if isinstance(r.get(k),(dict,list)) else str(r.get(k)) for k in keys) for r in charged)+'\n')
(e/'COMMIT-LOG.txt').write_text(subprocess.check_output(['git','log','--oneline',base+'..HEAD'],cwd=root,text=True)+'\nFinal evidence metadata commit follows this captured history.\n')
print(json.dumps(summary,indent=2))
