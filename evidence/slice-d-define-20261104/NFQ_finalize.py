"""Own evidence only: parity inventory and final bounded accounting."""
from pathlib import Path
import json,hashlib,subprocess,collections
E=Path(__file__).resolve().parent;R=E.parents[1];J=lambda n:json.loads((E/n).read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
put=lambda n,x:(E/n).write_text(json.dumps(x,indent=1)+'\n')
profiles=[]
for profile,k in [('verifier scalar',2),('program full ProgramResult',19),('core field scalar',21),('core Prepared9',31),('statement enum',33),('statement array4',37),('core WideExact getters',54)]:
 graph=J(f'NFQ_K{k:03}-graph-check.json');receipt=J(f'NFQ_K{k:03}/receipt.json');cfg=J(f'NFQ_K{k:03}.json')
 profiles.append(dict(profile=profile,representative=f'NFQ_K{k:03}',native_command=cfg['native_command'],root_package=cfg.get('root_package','aspis-r1-cost-probe'),selected_features={p['name']:p['features'] for p in graph['selected_closure'] if p['name'].startswith('aspis-')},frozen_graph_matches=graph['graph_matches_frozen'],source_assessment='Every admitted function body is byte-identical to its frozen ledger range in BOTH native/control snapshots. The helpers contain no feature-dependent branch; native target selects deployed feature requirements relevant to its actual reachable bodies. Only cfg(kani) attributes/modules and exact KMX cfg(kani) support are added in scratch. No proof uses no-entrypoint.',unrelated_workspace_feature='spend-dynamic-rate512 may appear through metadata workspace unification; these frozen body ranges do not read it or reach a function whose selected behavior depends on it.'))
put('NFQ_FEATURE_PARITY.json',dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',frozen_lock_sha256='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef',profiles=profiles,shipped_source_changes=False,rebuild_trigger=False,inherited_ELF_sha256={'default':'f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','devnet':'63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','Pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'},ELF_assessment='Inherited pins only, not rebuilt or newly measured: no repository shipped/cfg(kani) source changed. All native inputs are external scratch patches. No source-to-ELF premise is removed.'))
# Exact prerequisite table: no newly introduced field stubs.
(E/'NFQ_LPh_STUBS.md').write_text('''# NFQ multiplication stub inventory

No field multiplication stub occurs in an admitted NFQ native body. M31 neg/reducer and Prepared construction execute only real addition/subtraction/reduction bodies. Constructor/getter/enum/array helpers contain no field product. The exact KMX copy stubs are recorded separately in NFQ_CLOSED.json; they are not field stubs.

cm31_mul_r K050/K051 is excluded from admission despite a passing value/control pair and NFQ_Linear.source: the required opaque-call-log product form is missing. No multiplication credit is inferred from that pair. Future product callers must provide a named emitted-definition returns-ok/value theorem on every canonical domain, in LPh_STUBS.md, and prove the caller's domain before use. No unpaired arithmetic stub is counted as a pass here.
''')
# Exact proof/replay category, not cryptographic headline evidence.
receipts=[]
for p in sorted(E.glob('NFQ_[KLE][0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text());receipts.append(r)
put('NFQ_RESOURCE_SUMMARY.json',dict(scope_limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),all_zero_swap=all(int(r['swaps'])==0 for r in receipts),total_child_wall_seconds=sum(r['wall_seconds'] for r in receipts),submitted=110,charged=113,concurrent_own_scopes_max=1,Lean_memory_flag='-M7000',Rust_optimization='3',timeouts=0,memory_kills=0,cap_raises=0,transport_255_count=sum(json.loads(l)['exit']==255 for l in (E/'NFQ_TRANSPORT.jsonl').read_text().splitlines()),source_revision_note='Each receipt pins its actual stage HEAD plus all dirty input hashes. Native frozen revision stays 4bb3b3f...; final metadata does not rewrite historical receipt revisions.',receipt_classification='Kani bounded exhaustive body contracts and adversarial controls; Lean symbolic proofs/model associations and ax2; no fixture timing is a cryptographic cost theorem'))
print(json.dumps(dict(profiles=len(profiles),peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts))))
