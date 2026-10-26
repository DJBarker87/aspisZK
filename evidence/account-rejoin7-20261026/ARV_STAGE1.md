# ARV stage 1 — exact admission obstruction

ARV_Poison.entry retains every account data-cell handle, record, buffer, base and provenance, changing only each lamports-cell handle to its data-cell identity. ARV_Poison.snapshot/owned/sizes prove the owned TX2 and allocator inputs are unchanged. ARV_Poison.invalid/no_admission prove that this cannot satisfy any runtime admission (data/lamports cells must differ).

ARV_PoisonNative.accepted proves original TX2 native wrapper success transfers to this entry, with the altered heap as its actual returned heap. ARV_Constant.accepted proves the installed partial account accepts the constant adversary with that entry under the original extraction/syscall and native successes; ARV_Constant.no_support proves no At witness exists in any world. No constant-success native is introduced. These are conditional on the same real native successful pair as supplied at the root, not a newly inhabited pair. They are exact installed-account statements, not tiny-code analogy.

The malformed entry is outside the approved runtime-admitted game. Thus this is an abstract-experiment overcoverage finding, not a deployed attack. A universal accepted-world Supported theorem requires the experiment itself to enforce admission or a proof that such worlds have zero deployed failure under a genuinely equivalent deployed law. It cannot be inferred solely from an acceptance flag.

Attempts 001–007: five successful modules, two repaired development failures; all successful axioms are the three standards, no timeout/memory kill/swap. Full source, revision, dependency fingerprint, cap, wall/RSS and output receipts are retained per attempt. More work follows on the same-adversary adaptive counterexample and proposed root interface.
