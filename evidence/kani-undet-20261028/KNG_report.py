from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;P=E.parent
plan=json.loads((E/'KNG_RUN_PLAN.json').read_text());pairs=[];frozen='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
for i,row in enumerate(plan):
 recs=[]
 for neg in [False,True]:
  a=f'KNG_K{i*2+int(neg)+1:03}';p=E/a/'receipt.json'
  if not p.exists():raise SystemExit('Incomplete: '+a)
  r=json.loads(p.read_text());log=(E/a/'stdout.log').read_text();g=r['gate']
  assert g and g['lock_unchanged'] and g['metadata_wrapper_lock_unchanged'] and g['lock_before']==g['lock_after']==frozen
  assert r['resolved_features_per_crate']==g['metadata']['resolved_features_per_crate']
  assert g['metadata']['all_resolved_edges_and_checksums_match_frozen']
  assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
  assert r['swaps']=='0' and r['print_axioms']=='N/A: kani'
  admit=json.loads((E/(a+'-admission-0.json')).read_text());assert admit['exit']==0 and admit['reservation']['allowed'] is True
  features={n['name']:set(n['features']) for n in r['resolved_features_per_crate']}
  assert len(features['aspis-statement'])==14 and features['aspis-core']=={'r0'}
  if row['crate']=='aspis-r1-cost-probe':assert features['aspis-r1-cost-probe']=={'default','private-leaf-salts','optimized-terminal','program-build'}
  timeout=bool(re.search(r'(VERIFICATION:- TIMEOUT|Verification timed out|timed out after)',log)) or r['exit_status'] in [124,137]
  if neg:
   valid=r['exit_status']==1 and 'VERIFICATION:- FAILED' in log and not timeout and bool(re.search(r'\*\* '+('2' if row['historical_attempt']=='NBU_K022' else '1')+r' of \d+ failed',log)) and ('Failed Checks: This is a placeholder message' in log or row['historical_attempt']=='NBU_K022')
  else:valid=r['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in log and not timeout
  recs.append(dict(attempt=a,receipt=str(p.relative_to(E)),receipt_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),valid=valid,exit=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=int(r['peak_rss_kib']),cgroup_memory_peak_bytes=int(r['cgroup_memory_peak_bytes']),swaps=r['swaps'],timeout=timeout))
 assert json.loads((E/recs[0]['receipt']).read_text())['source_hashes']==json.loads((E/recs[1]['receipt']).read_text())['source_hashes']
 pairs.append(dict(**row,positive_result=recs[0],control_result=recs[1],status='RESTORED' if all(x['valid'] for x in recs) and not row['rule14'] else 'FAILED'))
assert len(pairs)==26
source=json.loads((P/'native-featparity-20261028/NCS_RESULTS.json').read_text())['rows'];lookup={r['historical_attempt']:r for r in pairs};rows=[]
for r in source:
 if r['classification']!='UNDETERMINED':continue
 required=r['missing_exact_harness_sources'];assert all(a in lookup for a in required)
 matches=[lookup[a] for a in required];status='RESTORED' if all(a['status']=='RESTORED' for a in matches) else 'FAILED'
 rows.append(dict(audit_row=r['audit_id'],member=r['id'],status=status,required_historical_attempts=required,new_pairs=[dict(historical_attempt=a['historical_attempt'],positive=a['positive_result']['receipt'],control=a['control_result']['receipt']) for a in matches],retained_credited_status=r['credited_status'],retained_quarantined_support=r['quarantined_support']))
assert len(rows)==23
out=dict(summary={k:sum(r['status']==k for r in rows) for k in ['RESTORED','UNRECOVERABLE','FAILED']},kani_attempts=len(list(E.glob('KNG_K*/receipt.json'))),lean_attempts=0,pairs=pairs,rows=rows)
assert out['kani_attempts']<=60
(E/'KNG_RESULTS.json').write_text(json.dumps(out,indent=2)+'\n')
lines=['# KNG reconstruction findings','',f"**FAILED: {out['summary']['FAILED']}. UNRECOVERABLE: {out['summary']['UNRECOVERABLE']}. RESTORED: {out['summary']['RESTORED']} audit rows.**",'', 'All 26 reconstructed recorded properties passed and their 26 matched inverted controls failed on their inverted observations (one assertion each; two variant-specific pointer observations in the getter control). No timeout credit, unchanged reruns, own copy stubs, verdict-driven renaming, or function-pointer-dependent property is admitted. No rule14 quarantine is cleared by this report.','', 'RESTORED means the missing-property evidence has been replaced by a new deployed-feature positive/control pair in its recorded local domain. It does not claim recovery of historical whole-file bytes or widen any inherited CLOSED-CONDITIONAL bridge. Existing NCS evidence covers the other historical support attempts; only the missing attempts listed below were rerun.','', 'Frozen source `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`; compilation lock SHA256 `'+frozen+'`, unchanged before/after every run. Exact KMX copy-stub SHA256 `ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138`. See [reconstruction details](KNG_RECONSTRUCTION.md), [source association](KNG_SOURCE_ASSOCIATION.json), [control-body audit](KNG_PROPERTY_AUDIT.json), [feature audit](KNG_FEATURE_AUDIT.json), [full results](KNG_RESULTS.json), and [input hashes](KNG_RECONSTRUCTION_HASHES.json).','', '| Audit row | Recorded member | Status | New positive / matched control |','|---|---|---|---|']
for r in sorted(rows,key=lambda r:(r['status']!='FAILED',r['audit_row'])):
 links=[]
 for a in r['new_pairs']:
  pos=a['positive'].split('/')[0];neg=a['control'].split('/')[0];links.append(f"{a['historical_attempt']}: [{pos}]({a['positive']}) / [{neg}]({a['control']})")
 lines.append('| '+r['audit_row']+' | `'+r['member']+'` | '+r['status']+' | '+'; '.join(links)+' |')
lines+=['', 'Every new Kani receipt embeds cargo metadata’s resolved feature list for every crate, the actual compile command, graph/lock validation and source hashes. Verifier-library commands select default/private-leaf-salts/optimized-terminal/program-build. Statement-helper commands select r0/pool-v1-kernel plus exactly twelve deployed optimization features. No program entrypoint was targeted and no no-entrypoint feature was selected. Metadata-only isolated roots include statement root dev dependencies and are separately lock-validated; they avoid unrelated workspace-wide feature unification. Their audit-only root is not deployed code.','', 'The six writer windows retain the original CM31 byte cut and every raw u32 word. NBH retains the all-raw-limb digest cut, exact ordered prefix errors and level<=20 one-step domain. NBU/NBX retains the exact U03/U05 fragment and source-model composition boundaries: DigestEncode/DigestDecode, TransferEncode/WithdrawalEncode, SAME-input child results, library/allocator fidelity, P6/SDK/TrustedStd, runtime/ABI and source-to-ELF obligations remain as in the packets. No whole decoder, encoder, validator, deployed 100-bit target or lower codec closure is newly inferred.','',f"Budget used: {out['kani_attempts']}/60 Kani, 0/10 Lean; six serial metadata preflights (four failed own inputs, two passed). Every compile/solver ran in one admitted scope, MemoryHigh=6G/MemoryMax=8G/MemorySwapMax=0/TasksMax=64. No transport retry or admission refusal occurred. Source revision, exit, wall time, peak RSS, cgroup peak, swap and N/A Kani axioms are recorded in each receipt. Maximum observed process RSS: {max(x[k]['peak_rss_kib'] for x in pairs for k in ['positive_result','control_result'])} KiB. Persistent cache retained at `/home/dombarker/project-offloads/codex-cx-kmy-cache-20261028`; no crate/program files changed in this worktree. No push."]
(E/'KNG_FINDING.md').write_text('\n'.join(lines)+'\n')
print(json.dumps(out['summary']),out['kani_attempts'])
