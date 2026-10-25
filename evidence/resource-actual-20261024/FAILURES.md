# Retained failures

Initial offline run: 11 tests, exit 1, 10 passed, one test setup error.
`test_missing_or_weaker_control_denies` called the historical synthetic legacy
fixture constructor after deleting `high`; the fixture's accounting raised
`KeyError: high` before the candidate evaluator. Corrected by constructing the
legacy observation before deleting the candidate control. No operational gate
change, live capture, scope, or resource failure occurred.

Pre-attempt staging bug: offline inspection of the exact transmitted bootstrap
showed `f.write('\\n')` in its Python source, which writes literal backslash+n
instead of a line terminator after JSON. Stage command exit 0 did not validate
manifest parsing. No live API call, attempt sentinel, or scope occurred. Replaced
with unambiguous `f.write(chr(10))`; expanded offline payload test to execute the
exact bootstrap in a private temporary stage and parse its manifest. Retain the
host malformed bytes separately, correct only own manifest, and verify pins.

Correction to the preceding staging diagnosis: exact remote bytes disproved it.
The displayed shell/Python escaping was misread. `staging-diagnostic-transport.json`
records size 110811 = expected JSON 110810 + one LF byte (tail 7d0a), with exact
expected prefix. The staged manifest was valid from the start. The repair guard
correctly failed `not the recorded staging failure`, exit 1, before any write.
No backup/rewrite happened. The repair script is a retained failed approach,
NOT an authorized retry entrypoint. The chr(10) change is clarity only and the
new execution/parsing test improves preflight. Earlier commentary's staging-bug
claim is withdrawn. No live capture, scope or attempt sentinel yet.

The single authorized live prospective capture is terminal DENY (exit 78):
`ValueError: invalid/overflow unsigned quantity`. Both full snapshots collected;
no collection failure was hidden. Before-snapshot system.slice parent anon
2,108,788,736 minus direct-child anon 2,122,874,880 = -14,086,144 bytes.
Exclusive current there is 1,085,534,208 bytes. Negative component is rejected
by unchanged accounting's `uint(value)`; full fallback only addresses a positive
recorded sum greater than current and cannot override this negative-component
rule. No rounding/tolerance claim or gate change. The after snapshot's anon
exclusive is +34,562,048, which does not repair the earlier snapshot or justify
using a different snapshot. No size search, second capture, scope or marker.
