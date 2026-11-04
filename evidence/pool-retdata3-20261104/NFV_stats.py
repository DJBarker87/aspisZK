from pathlib import Path
import json
E=Path(__file__).resolve().parent
rows=json.loads((E/'NFV_VALIDATION.json').read_text())['terminal_native'];assert len(rows)==80
passes=[r['attempt'] for r in rows if r['exit']==0]
timeouts=[r['attempt'] for r in rows if r['timeout']]
controls=[f'NFV_K{n:03}' for n in [9,11,*range(39,56,2),56,57,59,62,63,64,65,68,69,71,73,75,77,78,79,80]]
assert len(controls)==27
lookup={r['attempt']:r for r in rows}
assert all(lookup[a]['exit']==1 and not lookup[a]['timeout'] and not lookup[a]['unwind'] for a in controls)
assert len(passes)==18 and len(timeouts)==32
(E/'NFV_NATIVE_STATS.json').write_text(json.dumps(dict(positive_passes=passes,intended_failing_controls=controls,account_timeouts_no_credit=timeouts,incomplete_unwind=['NFV_K001'],deliberately_stopped_no_credit=['NFV_K060'],own_compile_failure_no_credit=['NFV_K066'],all_native_attempts=80,composed_NDT_rows_added=0),indent=1)+'\n')
print('18 scoped positives,27 intended controls,32 account timeouts,3 excluded/incomplete attempts; no new composed row')
