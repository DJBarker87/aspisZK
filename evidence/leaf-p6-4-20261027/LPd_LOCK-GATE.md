# Frozen lock gate and pinned Kani CLI finding

Frozen Cargo.lock is byte-identical to release 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:
SHA256 5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef.
The full scratch workspace, including that lock, is copied from the pinned
recapture tree. No standalone harness package is added to its dependency graph.

LPd_GRAPH001: cargo metadata --locked --offline succeeds. All 441 resolved
package tuples and every resolved dependency edge agree with the frozen lock
(444 lock entries; unused entries are not extra resolved packages). No version
or source substitution. LPd_GRAPH-CHECK.json retains the graph/feature inventory;
LPd_GRAPH001/stdout.log is the original metadata. The same preflight and lock
hash pass again immediately before LPd_K001.

The metadata graph reaches frozen cfg-if1.0.4/libc0.2.186; this inspection is
not a code-reachability proof that LPb's drifted dependencies were irrelevant.
Rule(c) therefore still requires frozen-lock native replay of the passing stages.
All eleven LPb passes are grouped into three planned replay harnesses; NONE
has yet been checked in this round. Existing LPb outcomes keep their qualification.

LPd_K001: pinned cargo-kani0.67.0 rejects the REQUIRED --locked flag:

    error: unexpected argument '--locked' found
    Usage: cargo-kani --manifest-path <PATH> --target-dir <TARGET_DIR>

Exit2, wall0.004563549s, peakRSS4400KiB, swap0. No Rust compilation, CBMC
verification, coverage witness or axioms audit occurred. --offline parsing
was not reached. LPd_kani-help.txt records the exposed CLI. Tool and unchanged
runner hashes are in LPd_tool-hashes.txt. This is a tool capability blocker,
not a counterexample, graph drift or a successful frozen replay.

Binding user rule(b) requires cargo kani with --locked --offline. local-lean
rule5 prohibits repairing build/launcher infrastructure. Stop native work;
do not remove these flags, repin, add a cargo wrapper or alter the toolchain.
Lead deliverable: an approved pinned invocation/tool capable of enforcing
both required Cargo flags, then resume the stage plan. No permission is inferred
from the successful independent metadata check.
