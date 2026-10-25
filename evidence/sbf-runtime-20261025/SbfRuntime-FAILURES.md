# Retained failed approaches

The only SSH metadata sequence returned 78. Payload
398c9320f0660e1be1b052b4e1f0c84d7f38ac06ea4fbe696d4501f6c77ec584
strictly requires every normalized symlink target to be immediately inside
/usr/bin, /usr/lib or /usr/local/lib. Its PT_INTERP walk encountered
`/usr/lib64` and denied. The exported error is exactly
`GuardError: symlink target outside public roots: /usr/lib64`.
The failing chain was not exported because the path walker returns its chain
only on success. No observation of the chain's remaining hops or endpoint
exists in this job. In particular this is a counterexample to the acquisition
payload's ability to close the loader under its configured prefix grammar,
not proof that the host has an unsupported final loader shape. Do not infer
an ownership failure, excessive runtime size, or host incompatibility.

The raw JSON has status UNKNOWN and is retained unchanged. This terminal error
exhausted the one-transport allocation. No path-policy repair, query, second
SSH, scope launch, backend call or guest execution followed.

The single local finite audit reached its receipt constructor after all
assertions and two output writes, then failed because local /usr/bin/python3
lacks sys.orig_argv. The command exit is 1, not 0. Preserve the exact source and
traceback; no repeat validation. A receipt-only reconstruction records the
missing metrics as UNOBSERVED rather than inventing a clean audit. Future
local harnesses must use a version-compatible argv capture. This failure is
separate from the remote 78 and never grants another host acquisition.

All six historical resource failures remain charged. No attempt changes any
compiler/Lean/Rust/Cargo/Kani/native/privileged/ELF budget.
