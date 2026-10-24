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
