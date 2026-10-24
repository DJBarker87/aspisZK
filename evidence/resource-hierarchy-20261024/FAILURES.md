# ResourceHierarchy failures and limits retained

The false cross-time claim E[k]>=0 is stopped: a parent read before a child's
later increment need not dominate that child read. No unique observed cause or
unseen error magnitude is established. No new physical safety result follows.
Original ResourceActual prospective DENY, ordered bytes/hash, report bytes/hash,
legacy result and all raw values remain immutable. The after anon +34,562,048
cannot repair the before anon -14,086,144. The old rule correctly rejected it.

Local attempt `python3 -B tools/resource-hierarchy-20261024/ResourceHierarchy_receipt.py audit-first`
failed before audit child execution: macOS rejected setting RLIMIT_RSS in
preexec_fn. Parent shell exit 1, wall 0.000003125s as reported by tool (not a
meaningful child time); child wall/RSS/swap N/A, no child was executed. Source
revision 0ae9700792; failed wrapper source hash was not captured before removal
of the unusable preexec block. Empty audit-first.json/log retained. This was
not an OOM, resource pressure, or permission to raise any host cap. Subsequent
small Python runs measure wait4 RSS and require <512 MiB; no process scan.

`audit-second` (receipt/log retained) failed because immutable legacy code's
self-source hash read was not redirected to pinned git bytes. The failure
occurred before consuming original first event; no real historical command
executed. Replacement intercepts read_bytes with preloaded immutable sources,
then checks all original events and both whole hashes. Candidate policy unchanged.
The first missing-interface synthetic scanner test also did not mock scandir
explicitly; it now mocks it, and the full audit hook rejects real directory scans.
No remote host read occurred.

`audit-third` passed six focused methods and original replay (receipt retained).
Expanded tests motivated a changed audit, not a repeat of unchanged regression.
`audit-fourth` failed immediately because the new no-filesystem-write audit hook
also blocked opening the git pipe file descriptor for writing. `audit-fifth`
allows descriptor pipes, still denies filesystem writes, and passed eight methods.
Full logs, exact command, revision and source/interpreter hashes, exit/wall/RSS/
swap are in each available receipt. No heavy build, memory failure, host scan,
cap increase, or live retry occurred. No failed source-fetch retry is authorized.

Historical 57 baseline +64 ResourceStat and 13 runner tests are REUSED receipts,
not new ResourceHierarchy validations. New tests use immutable fixture builders
without running those suites. Existing source/runtime/env/ELF pin assessments
remain historical, not a new identity gate. New synthetic GO checks do not
validate a fresh real scope or future consumer. Half-slab/reclaim estimates and
unseen/asynchronous memory behavior remain unproved.
