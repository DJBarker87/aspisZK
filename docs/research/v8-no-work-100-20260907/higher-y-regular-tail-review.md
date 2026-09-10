# Regular higher-Y support/query tail

Source parent: `e969d9fa5378dd1e548c8b64b79a9e76a2270d66`.
Status: exact arithmetic consumer of the checked direct-incidence theorem;
**not** a probability theorem, accepted-extraction partition or global
security result.

## Causal calculation

For a selected regular higher-factor candidate, let `m` be its actual number
of whole matching quotient fibres, fixed after alpha and before the queries.
`CoveredOriginalSymbols` gives at least `M=4m-2` matching original symbols.
The checked `HigherYRegularBranch.regular_branch_count`, followed by the
additive retained-factor budget, gives the proposed union tail

    H(m) <= floor(1048576*239599331/(4m-1026)).

This is a tail count: `H(m)` bounds gammas for which some qualifying selected
candidate has support at least `m`. It is not a count of independently chosen
candidate/gamma pairs. The maximal qualifying set can therefore retain an
adaptive post-alpha candidate without multiplying by the literal-family size.

If a total event adapter proves that the actual selected support has this tail
and that 22 fresh uniform distinct queries follow selection, layer-cake
summation gives, for residual selected supports at most `u`,

    1 / ((|QM31|-1)*choose(262144,22)) *
      [H(9558)*choose(9558,22)
       + sum(m=9559..u) H(m)*choose(m-1,21)].

The first term accounts for all schedules at the guaranteed minimum support;
the remaining summands use the exact identity
`choose(m,22)-choose(m-1,22)=choose(m-1,21)`. This is new information from
the proved support tail, not another use of the bare query-last identity.
A conservative `3/|QM31|` is additionally included for one nonzero cubic
fold residual in the arithmetic screen. It is not a substitute for the
shifted rho check or later relation-repair terms.

## Exact frontier

[`higher_y_regular_tail.py`](experiments/higher_y_regular_tail.py) computes
the integer sum and compares cross-multiplied integers against powers of two.
The checked output is
[`higher-y-regular-tail.json`](higher-y-regular-tail.json).

| Desired local bits | Largest residual support still passing | First failing support |
| ---: | ---: | ---: |
| 110 | 165,658 | 165,659 |
| 105 | 195,385 | 195,386 |
| 100 | 230,445 | 230,446 |

With no upper-support extraction cutoff, the whole regular tail has only
**96.0953599519 displayed bits**, including that conservative alpha term.
Thus the direct incidence plus queries is not by itself a 100-bit solution.
It becomes a potentially sufficient residual theorem only if a checked
payment extractor covers every regular selected execution above 230,445
matching quotient fibres; a useful global ledger would need a lower cutoff,
because 100.0000 bits leaves essentially no room for other events.

The 105-bit row gives a more realistic falsifiable target: prove checked
extraction for support above 195,385, or strengthen the incidence/semantic
classification. No such extraction implication is claimed here.

## Required theorem seams

The arithmetic applies only after proving all of the following:

1. actual repaired acceptance maps into the same fixed-factor regular class;
2. the image-valid original/quotient for a fixed regular prefix is unique
   before alpha, so the support being counted is not chosen to fit queries;
3. `M>=4m-2` uses the same selected quotient and actual received word;
4. queries are fresh uniform distinct fibres conditional on that complete
   prefix in the ideal game;
5. supports above the chosen cutoff yield a checked payment witness, not just
   a mathematical codeword.

The separate Fiat--Shamir lift must charge prequeries, retries, forks and
running time. Authentication, singular OOD rows, source refinement and
full-view zero knowledge remain outside this screen. No proof bytes,
verifier operation or transcript message changed; the body remains 40,282
bytes.

## Reproduction

```sh
python3 docs/research/v8-no-work-100-20260907/experiments/higher_y_regular_tail.py
```

On the local laptop this took 0.69 seconds and about17 MiB maximum RSS. The
saved JSON was compared byte-for-byte to fresh stdout and parsed with
`python3 -m json.tool`. Floating logarithms are display values only; every
pass/fail threshold is decided by exact integer cross multiplication.
