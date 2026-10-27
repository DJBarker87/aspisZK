# Option B statement audit (stage 1)

This is a **different theorem**, not a proof that the original deployed endpoint
has lost a premise. New module: `R1Z.PV_OptB_Endpoint`; theorem:
`privacy_headline_deployed_B`. Original:
`R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed`.
Both are printed side by side in the stage-1 compile output.

## Binders and carriers

Retained verbatim: implicit `CommitHandle Aux`, `template`, `outputs`, public
statement `x`, `rust`, its finite/nonempty real randomness instances,
`observer_program`, and original `RustRealRefinement`. All universal adversary,
witness and public-equality binders remain. The local honest prover is the
same `BuilderSource.prover`; the new namespace's `input` unfolds to that term.

Added: implicit error/observation carrier `E : Type`,
`failure : E → rust.Adversary → ROMView K CommitHandle Aux R1Bat`, and
`signal : Option E`. `E` must retain which call failed, position and error plus
any complete observed prefix; it cannot silently erase side channels.
`failure` receives no witness. This syntactic restriction does **not** prove
that a signal extracted from the actual caller is witness-independent.

Neither real nor ideal random carrier changes: `rust.RealRand` and the original
reencoded source's `IdealRand` are retained. `none` means the old experiment;
`some e` means the same complete failure view is supplied to both worlds.
This stage is a fixed-public-signal theorem, not a conditional-distribution
claim about an endogenous signal correlated with successful execution coins.

## Conclusion terms

Only the two tests inside the distinguishing advantage change:

- `realTest h B outputs rust adv x w` becomes `realTestB … failure signal adv w`.
- `idealTestS source (RomObserverBin.observerMap rust observer_program adv) x
  (simE (h).transport B outputs x)` becomes `idealTestSB … failure signal adv`.

For `none` these reduce to the exact old tests. For `some e` both tests are
`fun _ => bit (rust.observe adv (failure e adv))`. The complete observer is
unchanged. The old `simE`, observer map, source encoding, eight-attempt model,
and all terms of both numerical conjuncts are unchanged. No simulator is
replaced by a witness-bearing function.

## Why the bound is unchanged

For `none`, use the original theorem. For `some e`, both means are the same
constant, so the advantage is zero, bounded by the original nonnegative
bound. Both numerical conjuncts are copied directly from the old theorem.
No extra probability mass is charged and no bad event is enlarged.

## Premises before/after

Stage 1 retains the original `RustRealRefinement`; zero endpoint premises
removed. `OsAvailable` is not a binder of the original theorem; it occurs only
in the separate preparatory available-option theorem. Its removal cannot be
claimed as removal from the original theorem. The substantive gap is the
complete native/source agreement on OS-error worlds, hidden in RunJoin's
outside-bad equality / V038 trace obligations. Stage 3 must replace that
agreement by a proved public-failure-aware agreement, not retain an impossible
old agreement while claiming closure. The capped trust list is unchanged.

## Continuation outcome

The B statement remains the separate fixed-public-signal theorem described
above. The resumed investigation has not proved its signal is the endogenous
failure signal of the extracted deployed caller on every admitted witness.
The conditional `PV_OptB_DeployedSignal.conditional_independence` exposes the
remaining body-step synchronization P premise; it does not discharge it.
No original premise is removed. No T field, simulator change, observer
restriction or enlarged numerical bound has been introduced. Stage 3 is
unfulfilled, and the privacy target is not yet established.

## D262 continuation: adopted off-bad condition

The earlier all-world `PV_OptB_Factorization.Independent` condition is
superseded for option B. It is retained as a historical definition; it is
not required by the adopted condition. New declaration (private overlay,
module `R1Z.PV_OptB_OffBad`):

```
IndependentOffBad pub signal bad :=
  ∀ w u, pub w = pub u → ∀ os coins,
    ¬ bad w os coins → ¬ bad u os coins →
    signal w os coins = signal u os coins
```

`w,u` range over the honest prover's admitted `Instance`. `os` and `coins`
are literally common inputs. `signal` must be the reached observation:
`none`, or exact call family/position/error and any observed prefix. The
fixed native HOST_HASH belongs to the interpretation, not a witness-selected
oracle. Neither `simE` nor the full observer changes.

`PV_OptB_Charged` spells the existing event names on explicit coordinates:
`HvzkV.poleBad`, `QueryScanRealLazyBound.lazyBad` (the conservative
honest-read collision/digest exception), `FinalR1PBin.exhQ` (mask exhaustion
or digest hit), `QueryScanRealFreshMass.realFresh`,
`QueryScanRealLazyBound.realBad` (parser/scan failure),
`ProverCommitSeedEvent19.seedGuess`, and `ProverCommitFuelJoin22.failure`.
These are existing events, with existing allowances only. There is no
OS-unavailability bad event and no new probability charge. The coordinates
into their different coupling spaces are data; their common native
interpretation is still a proof obligation. An abstract event union on
arbitrary maps is not a certified native union or a new mass theorem.

The source's public `P_R1` failure and mask exhaustion can also produce
`Rejected` (`prover.rs:169–184,345–347`). Thus the usable off-pole fact is
`P ∧ V(w) ↔ P`; it does not assert that no public rejection occurs. This is
the exact `HvzkS.hybrid_ideal_leS`/`HvzkV.firstGood_congr` route.

Before: all-world fiberwise independence; after: independence on the good
part of each public fiber. Proved generically: equivalence with a decoder
`Public → World → Coins → Option Event` agreeing only off bad. Not yet
proved: the emitted caller's native instance, event-coordinate association,
or the endogenous joint experiment transport. Endpoint premises removed: 0.
