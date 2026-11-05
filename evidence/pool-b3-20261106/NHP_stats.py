from pathlib import Path
import json,collections
E=Path(__file__).resolve().parent;rows=[json.loads(l) for l in (E/'NHP_ATTEMPTS.jsonl').read_text().splitlines()];ids=[r['attempt'] for r in rows]
assert len(ids)==len(set(ids))
used={k:sum(a.startswith('NHP_'+p) for a in ids) for k,p in [('kani','K'),('lean','L'),('extraction','E')]};assert used==dict(kani=120,lean=23,extraction=2)
categories=collections.defaultdict(list)
for row in rows:
 a=row['attempt'];text=(E/a/'stdout.log').read_text();rc=json.loads((E/a/'receipt.json').read_text());assert int(rc['swaps'])==0
 if not a.startswith('NHP_K'):continue
 shape=json.loads((E/(a+'-shape.json')).read_text());mode=shape['mode']
 if 'CBMC timed out.' in text:category='tool_timeout'
 elif 'VERIFICATION:- SUCCESSFUL' in text:category='successful_local_observation'
 elif 'VERIFICATION:- FAILED' in text and 'negative' in mode:category='expected_control_failure'
 elif 'VERIFICATION:- FAILED' in text:category='retained_finding_or_mismatch'
 else:category='compiler_or_harness_input_rejection'
 categories[category].append(a)
pairs=[(1,2),(6,7)]+[(i,i+1) for i in range(8,26,2)]+[(28,29)]+[(i,i+1) for i in range(30,68,2)]+[(69,70)]+[(i,i+1) for i in range(72,86,2)]+[(i,i+1) for i in range(87,95,2)]+[(i,i+1) for i in range(96,104,2)]+[(104,105)]+[(i,i+1) for i in range(106,114,2)]+[(114,115),(116,117),(118,119)]
pairs=[dict(positive='NHP_K'+str(p).zfill(3),control='NHP_K'+str(n).zfill(3)) for p,n in pairs]+[dict(positive='NHP_K069',control='NHP_K071',property='Borsh string byte'),dict(positive='NHP_K096',control='NHP_K120',property='aliased data frame')]
for p in pairs:
 assert 'VERIFICATION:- SUCCESSFUL' in (E/p['positive']/'stdout.log').read_text()
 assert 'VERIFICATION:- FAILED' in (E/p['control']/'stdout.log').read_text()
(E/'NHP_NEGATIVE_CONTROLS.json').write_text(json.dumps(dict(pairs=pairs),indent=1)+'\n')
summary=dict(used=used,limits=dict(kani=120,lean=80,extraction=2),wall_sum_seconds=sum(float(r['wall_seconds']) for r in rows),peak_rss_kib=max(int(r['peak_rss_kib']) for r in rows),swaps=0,categories=dict(categories),matched_controls=len(pairs),memory_kills=[],unchanged_timed_out_shape_replays=[],closed_rows=2,source_revision_note='Each receipt records exact then-current revision, dirty flag, source/dependency hashes and argv; final commits contain the byte-identical inputs.',new_runtime_assumptions=[],pending_runtime_rows_used=[],shipped_source_changed=False,release_elf_rebuilt=False,pushed=False)
(E/'NHP_STATS.json').write_text(json.dumps(summary,indent=2)+'\n');(E/'NHP_BUDGET.json').write_text(json.dumps(dict(limit=summary['limits'],used=used),indent=2)+'\n');print(json.dumps({k:summary[k] for k in ['used','wall_sum_seconds','peak_rss_kib','swaps','matched_controls']}));print({k:len(v) for k,v in categories.items()})
