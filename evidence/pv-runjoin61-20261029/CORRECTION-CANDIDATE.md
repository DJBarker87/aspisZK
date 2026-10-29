# Residual circle dictionary: proposed correction, not applied

The nine historical link bodies, ActualRun families, Produced predicate,
CaptureFactorSource60 and CapturedTransport60 are unchanged.

The concrete selected dictionary is still parameterized by arbitrary residual
`ops : ExternalFuns`. Unlike op12 (already overwritten by its native source),
`op259` is preserved from ops, by `CircleInstalled52.installed_projection`.
It is not silently installed by WeightInstalled46.selected.

## Before

An unconditional success proof uniformly over arbitrary residual ops:

```
forall base heap box ops,
  letI := types base
  letI := selected base heap box ops
  Nonempty {p : Phase // ActualProvenance60.Produced p}
```

This universal statement admits a diagnostic ops with op259 diverging on
all blocks and both circle rows. Every produced phase must have reached
both circle calls. Such an ops therefore has no produced phase. This is a
counterinstance to that universal statement, not a finding that the deployed
sampler diverges, and not a nonempty model witness.

## Proposed after (requires source dictionary binding, not adopted here)

Keep the exact nonemptiness obligation and all nine exact link bodies.
Identify the residual op259 used by the native caller with the retained native
circle sampler, then prove the symbolic success conditions in that fixed
source dictionary. `CircleNeutralSelected52.selected` is an existing explicit
candidate installation; merely selecting it does not prove that the original
native caller uses it. The equality/transport to that caller must be proved.

CommonSample's circle unit and canonicality arguments require this source
association or an independently proved caller-specific law for the actual
op259 results. Extracting a successful abstract op259 call alone does not
supply its coordinate laws. The source-dictionary association is a fact about
the installed operation, not a new assumption about a produced phase. It must
remain a proof obligation, never a fourth TrustItem or a silent premise on
CommonSample.

No corrected theorem or endpoint is claimed. An existential model instance
with a properly chosen dictionary remains a permitted alternative; the
universal counterinstance does not refute that alternative.
