Capacity resume 2 — native repeatability boundary (work in progress)

Recovered clean checkpoint bc957add0a. Count before new work: 49/100 Lean,
29 passes/20 rejected inputs; 0/10 Kani. Next ID20949; 51Lean remain.
No previous attempt is discarded on automatic relaunch.

Owner branch read-only pin c108ae7a62: more arithmetic callbacks supplied,
but whole proof/audit/native-effect association remains unproved. No owner
modules or worktrees were edited or read through the live filesystem.

The proposed fixed-dictionary full-native equality is tested directly at the
shipped source helper generate_for_mask_nonce. The probe copies its body,
nonzero helper, struct, error and error conversion verbatim (source hashes
retained); actual getrandom0.3.4/zeroize1.8.1, no stub or mocked callback.
Its only input is a fixed public nonce [1;32], not a wallet/account key. It
checks two native calls return distinct private output; only Booleans are
logged. Private entropy is owned by the source's actual Zeroizing wrappers.
This is a source-helper check, not an SBF/artifact or full-prover check.

Native attempt1 compilation exits101: probe's unwrap required the source's
Debug attribute, omitted by the textual fragment selector. No helper logic
failed. Changed probe uses explicit Result matching, preserving every copied
fragment; actual Linux transitive dependencies cfg-if/libc are also pinned to
the repository lock. Rejected source and logs retained on host; no unchanged
rerun. Before changed native attempt2 the admission gate refuses reservation
at10:48:08 UTC:51,942,260,736reserved+8GiB exceeds55GiB. No scope launched.
Wait180seconds before a fresh admission check; no gate/launcher/cap changes.

Before/after theorem claim (pending compilation): if two native successes at
one public nonce have distinct secret representations, no ONE pure ExternalFuns
dictionary can make the actual emitted generate_for_mask_nonce equal both.
An injective representation map does not repair this contradiction. A dictionary
chosen once per whole sample still has this obstruction. This does not rule
out an effect-aware interpreter, state-passing transformation, distributional
refinement, or a weaker sufficient observational relation.

No proposed deployment field is discharged by this boundary check. Endpoint
fields3→3(V037;twoV038),fixture association2→2(V047);V045's full effect/world
installation remains absent. No full deployed-premise record or rust instance
is manufactured. Original bad, observer, simulator and guard remain unchanged.
