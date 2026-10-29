"""Offline receipt/source audit; never launches a compiler or changes host state."""
from pathlib import Path
import hashlib, json, re
E = Path(__file__).resolve().parent
R = E.parents[1]
plan = json.loads((E.parent / 'native-reconcile-20261028/NDO_RETARGET_PLAN.json').read_text())
expected = [r['module'] for r in plan]
standard = {'propext', 'Classical.choice', 'Quot.sound'}
summaries, passing, failures = [], set(), []
for receipt in sorted(E.glob('NDR_B[0-9][0-9][0-9]/receipt.json')):
    raw = receipt.read_bytes()
    row = json.loads(raw)
    attempt = row['attempt']
    log = (receipt.parent / 'stdout.log').read_text()
    admission = json.loads((E / (attempt + '-reservation.json')).read_text())
    assert admission['allowed'] is True, attempt
    assert row['limits'] == {'memory.high': '6442450944', 'memory.max': '8589934592',
                             'memory.swap.max': '0', 'pids.max': '64'}, attempt
    assert str(row['swaps']) == '0', attempt
    axioms = set()
    for line in row['print_axioms']:
        match = re.search(r'depends on axioms: \[([^]]*)\]', line)
        if match:
            axioms.update(x.strip() for x in match[1].split(',') if x.strip())
    completed = re.findall(r'^NDR_END (\S+) 0$', log, re.M)
    assert all(m in row['modules'] for m in completed), attempt
    if row['exit_status'] == 0:
        assert completed == row['modules'], attempt
    else:
        failures.append(attempt)
    # Credit only finished modules, including successful prefixes of failed chunks.
    segments = dict(re.findall(r'^NDR_BEGIN (\S+)\n(.*?)^NDR_END \1 0$', log, re.M | re.S))
    for module in completed:
        name = module + '.lean'
        assert hashlib.sha256((R / 'lean' / name).read_bytes()).hexdigest() == row['source_hashes'][name], name
        for used in re.findall(r'depends on axioms: \[([^]]*)\]', segments[module]):
            names = {x.strip() for x in used.split(',') if x.strip()}
            if module == 'NDO_JHs_PDA' and 'choice' in names:
                assert '\nopen Classical\n' in (R / 'lean' / name).read_text()
                canonical = json.loads((E / 'NDR_L004/receipt.json').read_text())
                assert canonical['exit_status'] == 0 and len(canonical['print_axioms']) == 9
                assert all('Classical.choice' in line and 'choice,' not in line.replace('Classical.choice,', '') for line in canonical['print_axioms'])
                names = (names - {'choice'}) | {'Classical.choice'}
            assert names <= standard, (attempt, module, used)
    passing.update(completed)
    keys = ['attempt', 'modules', 'exit_status', 'wall_seconds', 'peak_rss_kib',
            'swaps', 'source_revision', 'limits', 'cgroup_memory_peak_bytes']
    summary = {k: row[k] for k in keys}
    summary.update(full_receipt=str(receipt.relative_to(E)),
                   full_receipt_sha256=hashlib.sha256(raw).hexdigest(),
                   completed_modules=completed, printed_axioms=sorted(axioms),
                   axiom_audit_lines=len(row['print_axioms']),
                   printer_alias_note=('NDO_JHs_PDA opens Classical; choice prints Classical.choice; canonical full-name audit NDR_L004 confirms Classical.choice' if 'choice' in axioms else None))
    summaries.append(summary)
assert passing <= set(expected)
result = dict(passing_modules=len(passing), planned_modules=len(expected),
              missing_modules=[m for m in expected if m not in passing],
              failed_chunks=failures, completed_chunk_receipts=len(summaries),
              status='all planned modules verified' if len(passing) == len(expected) else 'partial; no release claim')
(E / 'NDR_BUILD_RECEIPTS.json').write_text(json.dumps(summaries, indent=2) + '\n')
(E / 'NDR_VERIFICATION.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k != 'missing_modules'}))
