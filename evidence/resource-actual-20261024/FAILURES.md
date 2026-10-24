# Retained failures

Initial offline run: 11 tests, exit 1, 10 passed, one test setup error.
`test_missing_or_weaker_control_denies` called the historical synthetic legacy
fixture constructor after deleting `high`; the fixture's accounting raised
`KeyError: high` before the candidate evaluator. Corrected by constructing the
legacy observation before deleting the candidate control. No operational gate
change, live capture, scope, or resource failure occurred.
