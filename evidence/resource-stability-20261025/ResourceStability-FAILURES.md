# Retained failures

focused-first: runner bootstrap exit 1 before importing the target. Darwin
rejected setrlimit(RLIMIT_AS, 512 MiB) with "current limit exceeds maximum
limit" despite reported infinite limits. A separate tiny RLIMIT_DATA preflight
also rejected lowering with the same message. No evaluator/test/replay ran and
no memory pressure occurred. Source and exact bootstrap receipt/log retained.
Replacement runner uses bounded offline inputs and records/checks actual peak
RSS <512 MiB. It does not claim an enforced OS address-space cap. No build or
host work is involved; all such budgets remain zero.

focused-second: eight new groups, seven pass and one fixture error. The intended
valid-topology-addition case added a default 1 GiB current to a fixture whose
root residual was already zero. Unchanged uint subtraction correctly denied
negative residual before the intended structural-race assertion. Replacement
sets that new node's current explicitly to 0 (cap still 1 GiB); no evaluator
change or error relaxation. Receipt records failed source hashes and traceback.

audit-first: reconstruction stopped at the ordered-stream pin assertion before
calling the original API. The new audit compared a two-field digest dictionary
against an original export pin that also contains `name`. Replacement compares
exact sha256 AND size explicitly, as the original audit does; name/path selection
remains exact. No event/source/report bytes or evaluator changed. Failed audit
receipt/log retained. This was audit bookkeeping, not a historical denial or a
counterfactual result.

audit-second: original14926 API input/report reconstruction completed, but new
audit expected its full diagnostic delta to equal the old membership-only race
detail. That old projection intentionally omitted pids.current. Complete inputs
also record counts decreasing by one at five ancestors/leaf (13→12,13→12,
10→9,7→6,3→2), consistent with the lost thread. The evaluator correctly retained
these differences. Replacement audit checks the exact old membership delta AND
all five raw count deltas. No scanner/evaluator/source receipt fields dropped.
No counterfactual result was sealed on that failed attempt. Failed receipts and
logs retained; the changed audit and missing final packet justify completion.
