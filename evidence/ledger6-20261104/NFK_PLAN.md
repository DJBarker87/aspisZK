# NFK authoritative refresh

Extend the exact NEZ 202/587 checkpoint by additive, receipt-backed admission checks. No Lean, Kani, native build, host launch, wallet operation or push. Only NFK files in this directory change.

Stages: (1) record policy and immutable source selection; (2) implement additive certificate admission, trust tagging, qualification, audit checks and mutations; (3) generate and reconcile the final ledger and handoff.

Source baseline: 9905ea55a106eadbf120088a8b7601c6fa7c2843. This tree removes NFJ's entire evidence directory after merge eeaa04cfaf3. NFJ inputs therefore come explicitly from that immutable merged revision, using Git objects read-only. This is historical receipt reuse, not a fresh execution or a claim that HEAD contains the missing evidence. All consumed Git blobs are recorded by revision and SHA256. Existing successful proof/validator receipts are reused; no unchanged full regression is repeated.

Rules read: /Users/dominic/ZK/AGENTS.md sections 3 and 8; local-lean.txt rules 12–15; task AGENTS. Retain all exclusions; RuntimeReturnData(ab) and RuntimeMemcmp(ac) are ADDED trust pending owner confirmation. NFB TX1:181/TX2:104 remain QUALIFIED until a separately merged coherent replay (NFG is outside this refresh). NEV's four rows require NFC's ax2 fixture receipt and NFA's standard-only raw audit.
