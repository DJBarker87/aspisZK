from pathlib import Path
import json
E=Path(__file__).resolve().parent
credits=['C044','C084','C088','C089','K93109','K93110','K93111']
runs=json.loads((E/'runs.json').read_text());rows=[]
for c in credits:
 d=json.loads((E/(c+'.json')).read_text());rr=[r for r in runs if r['credit']==c]
 metrics=[json.loads((E/'host'/r['id']/'receipt.json').read_text())for r in rr]
 d['harnesses']=[r['command'][r['command'].index('--harness')+1]for r in rr]
 d['scopes']=['pv-k4trace-'+r['id'] for r in rr]
 d['source_identity']=['host/'+r['id']+'/identity.json'for r in rr]
 d['metrics']=[{k:m[k]for k in ['id','exit_status','wall_seconds','peak_rss_kib','swap','cgroup_peak_bytes','cgroup_swap_peak_bytes']}for m in metrics]
 d['Kani_version']='0.67.0';d['CBMC_version']='6.8.0';rows.append(d)
status={'task':'LOG D645','branch':'codex/pv-k4trace-20261104','base':'670416be996ba5a0e1c5fb6349a7db34f16714d0','credits':rows,'recommendations':{r['credit']:r['classification'] for r in rows},'V177_V180':rows[0]['V177_V180'],'Lean':0,'endpoint_premises_removed':0,'endpoint_premises_added':0,'endpoint_premises_weakened':0,'recount_and_ledger_edited':False,'implementation_or_harness_edited':False,'extra_attempts':{'K93500':'pre-compiler CLI validation error; exit2','K93501':'raw-output-mode reachability-probe failure only; not used as positive; see OUTPUT-MODE.md'},'remaining_boundaries':'Original std parity/k\'\'\', V370/compiler-cohort, copy-stub/native association, allocator/world and privacy endpoint obligations are retained. Original ptr.add/allocation/OWNER association is OPEN; projection results do not supply it.'}
(E/'k4trace-status.json').write_text(json.dumps(status,indent=2)+'\n')
s='''# D645: retained matched-control execution traces

Branch `codex/pv-k4trace-20261104`, base `670416be996ba5a0e1c5fb6349a7db34f16714d0`; worktree `/Users/dominic/ZK/.worktrees/pv-k3scan`. Receipts are confined to this directory. No implementation, harness, assertion, bound, cap, recount or ledger edits; 0 Lean and `#print axioms` N/A. No push.

These are recommendations for Recount 13, restricted to each original qualified credit. All source files and six executable hashes are checked against retained pins before each launch. Exact historical C084 and projection source snapshots are replayed privately because the current host copies have since changed; preflight.json discloses those differences. Recovery changes no source bytes. Source packages and provenance are retained in source-payload.json.xz, source-provenance.json and retained-k3-sources.json.xz. Original commands/receipts are under original/.

Pinned Kani 0.67.0, bundled rustc 1.93.0-nightly (53732d5e0), CBMC 6.8.0 and kissat 4.0.1 match original/tools.json by SHA-256. K93109–K93111 original receipts record the harness revision/command but no per-run executable hashes; the standing globally pinned installation is checked against the retained Kani/CBMC executable pins rather than inventing historical per-run hashes. No toolchain is installed or changed. Existing std-transfer and compiler-cohort qualifications remain.

Every run uses one scope at a time, MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64, CPU0–3, original solver/timeout/features and original optimized profile. C084 preserves its original dev-profile defaults (opt-level=3); the other packages explicitly disable debug assertions and overflow checks. Both admission checks require allowed:true and exit0; quiet-marker snapshots and 180-second spacing are retained. Wall/RSS columns list the scopes in the displayed order. Peak RSS is GNU time's maximum process RSS in KiB; the receipt also retains aggregate cgroup memory peak bytes. Swap is both GNU time and cgroup swap peak.

| Credit | Harness/filter | Source SHA-256 (complete primary file) | Kani | Scope IDs | Wall seconds | Peak RSS KiB | Swap | Positive verdict | Control verdict | Trace location | Classification |
|---|---|---|---|---|---|---|---|---|---|---|---|
'''
for d in rows:
 m=d['metrics'];s+='| '+' | '.join([d['credit'],' / '.join(dict.fromkeys(d['harnesses'])),d['source_sha256'],'0.67.0',' / '.join(x['id']for x in m),' / '.join(f"{x['wall_seconds']:.3f}"for x in m),' / '.join(str(x['peak_rss_kib'])for x in m),'0',d['positive_verdict'],d['control_verdict'],d['location'],d['classification']])+' |\n'
s+='\nFull scope IDs are `pv-k4trace-<ID>`. For each scope, `scope-command.json`, `STARTED.json`, `identity.json`, `metadata.json`, `receipt.json`, `time.log`, `cbmc-*-command.json`, full raw `cbmc-*.json[.xz]`, and `symbols-index.json` retain the exact execution and symbol mapping. The positive C044 cached goto symbol dump was recovered read-only inside its control scope K93502, explicitly indexed by the K93512 command receipt. K93500 and K93501 are disclosed in OUTPUT-MODE.md; neither is substituted for a green positive. K93501\'s apparent failure is fully classified as raw reachability-probe reporting, with no failing program property. The transparent tee forwards the unchanged CBMC stdout to the unchanged pinned driver, preserving normal Kani verdict processing.\n\n'
for d in rows:s+='## '+d['credit']+'\n\n'+d['reason']+' Full trace and numbered excerpts: '+d['trace_excerpt']+'.\n\n'
s+='''## Consequences and retained obligations

'''+rows[0]['V177_V180']+'''

C084 does not supply V179's current independent structural support. C088/C089 do not replace C002 or discharge V233's independent typed/native association. K93109–K93111 cover only the segregated logical-offset/two-place projection; the original ptr.add/allocation/OWNER association remains OPEN. Every historical K-1/K-2/K-3, copy-stub, std parity/structural k\'\'\', feature, compiler V370 and world qualification is retained. No new T field or endpoint premise is introduced.

Before/after endpoint statements are unchanged: PrivacyR1HeadlineDeployedReal.privacy_headline_deployed loses no premise and gains no premise. E1/E2, actual RunJoin, proof-account client, L1/L2/L3, coherent dependency replay and axioms obligations remain. Privacy target not established. The next action is for the lead to feed these per-credit decisions into Recount 13; this job does not edit those authoritative files.
'''
(E/'K4TRACE.md').write_text(s)
print(status['recommendations'])
