# R594: joint challenge mass

R594 proves the exact ordered four-tuple target mass for the existing source-shaped ordinary `challengeProgram` under independent raw calls. The formula is

```text
((1 − (1 / 2147483648)^8) / 2147483647)^4.
```

It accounts for the shared cursor, eight attempts per limb, rejection and stopping behavior.

## Verification

- Canonical source: `lean/AspisV8R19/R594JointChallengeMass.lean`
- Original draft: `.r21-scratch/R594JointChallengeMass.UNVERIFIED.lean`
- Canonical/draft SHA256: `e67591dce5709988ff99671d1ce157e8d9db5ec85a9de53b9bb31bf31055f5c8` (byte-identical)
- Final canonical target receipt: `1791088944070459000`
- Source revision: `92b64e72c1b59fe6506be9e3e45e52b217af5869`
- Result: exit 0; wall 1.24 s; Lean-child peak RSS 3,260,388 KiB; swap 0.
- Resources: `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`; Lean `-j1 -M4500`.
- Two complete final `#print axioms` reports use only `[propext, Classical.choice, Quot.sound]`.

The evidence preserves failed focused attempt `1791088917534278000`, caused by an unknown `blockAnswer` namespace and default rewrite recursion. The final proof uses an explicit observer/namespace and `maxRecDepth=4096` under the same caps. Sources, logs, receipts, direct pins, runner, publish paths, and a SHA manifest are in `evidence/r594-joint-challenge-mass/`. No check was rerun for this promotion.

## Boundary

R594 is an exact mass result for the abstract independent raw-call program. It does not establish i.i.d. behavior of the actual memoized shared oracle, native-wrapper correspondence, a full published view, privacy, or security.

The first remaining step is the actual shared-oracle history and collision loss, followed by the accepted-circle conditional law.
