# Selected semantic terminal alternative

Status: **V5 GREEN and frozen**, with seven standard-only axiom audits.
Source: [SelectedSemanticTerminalAlternativeV5.lean](experiments/SelectedSemanticTerminalAlternativeV5.lean),
SHA256 `1416ad6581d054c76885d2f0942b147c36599a4472013cc7945c4dfb9ba71f48`.
It imports only checked `SelectedCompactSemanticRepairV4` and
`SelectedSemanticLaneAggregationV2`. All five exact attempt snapshots/logs/
manifests are retained locally; only V5 receives theorem credit.

## Exact outcome, not an authentication assumption

`selected_terminal_alternative` substitutes the SAME selected29 Boolean
table, equality-point weights, helper and active mask into the compact
ten-round recurrence. Its result is:

- all 29 row coefficients and both helper sums vanish, or the named
  theta / equality-point / quadratic-mu collision occurs; or
- the initial claim is not the fixed mask sum; or
- the computed compact terminal is not the fixed reference terminal; or
- an actual round challenge hits the claimed/reference degree-27 bad set.

The first grouped alternative is exactly the checked
`source_zero_alternative`, with bounds 28, 10/|K|, and 2 at its distinct
fixing stages. The reference table is literally
`mask + eta * realTable`, not a caller-supplied placeholder equality to some
unrelated oracle. The eta nonzero premise is explicit. Initial-mask and
terminal-opening authentication failures remain named, unbounded alternatives;
no scalar acceptance check is promoted to their absence.

The conclusion applies to any compact transcript meeting the displayed
source-to-plan interface, and hence to an accepted subset. It does not claim
that the actual byte decoder or commitment system supplies that interface,
or that all accepted traces have a common authenticated table.

## Adaptive finite mean

`Plan` supplies claimed and reference degree-at-most-27 polynomials as
functions of the strictly earlier challenge history. `Plan.bad` is empty
when they coincide and otherwise contains the roots of their difference
in the original finite domain S. Every such set has at most 27 elements.

`failure S plan n history` is the exact ideal fresh-answer tree mean. A hit
pays one and ends the charged event; otherwise the next bad set is chosen
from the extended history. `failure_unit` proves it is in [0,1], and
`failure_bound` proves `n*27/|S|`; `ten_round_bound` specializes to
`270/|S|`. No independence among the adaptive bad sets is assumed and S is
not conditioned or renormalized.

V3 proves this induction in `FiniteMean.bound` over an arbitrary type A and
an arbitrary prefix-indexed collection of finite bad sets with cardinality
at most d. No field, Plan record or polynomial occurs there; the selected
plan probability is only its specialization at d=27. V1/V2's proof-plumbing
timeouts remain diagnostics, not failed mathematical claims. Module limits
remain depth 200 and 200,000 heartbeats. Only the `repair_hits_plan`
declaration/proof/linter has a local depth-400 allowance, solely for static
type/instance conversion at its two already-proved generic applications:
`repair_hits_badRound` and `Plan.mem_bad_of_equal`. There is no finite-domain,
polynomial or recurrence normalization there and no memory/heartbeat
increase. All other declarations, including `FiniteMean.bound`, remain at
depth 200. The V4 diagnostic specifically identifies the second application
and linter, after the first application had been isolated.

`FollowsPlan` identifies the actual compact message and the reference
message at each history. `repair_hits_plan` derives actual repair membership
in that plan's bad set. This is a one-run deterministic transport. Applying
the fixed-plan mass bound to a source event requires ONE prefix-fixed plan
that satisfies this transport across the entire challenge experiment. It is
not sufficient to choose a different plan retrospectively for each finished
transcript. A source-to-fresh-answer-law theorem is still separate.

The exact counterexample to retrospectively choosing the plan is the family
`P_r(X)=X-r`: each fixed polynomial has only one root, while choosing `P_r`
after seeing r makes the root event certain. This does not assert source
acceptance or a same-table authenticated execution; it pinpoints why the
single-run transport cannot discharge the global fixed-plan premise.

## Reuse and chronology

The finite-mean induction narrowly reuses the mathematical argument in
`V5AdaptiveSumcheckChallengeBound` / `V5FiatShamirAdaptiveQueryBudget` through
the already-pinned `JointImageGame.avg_exception`, rather than importing
their thirty-module unregistered closure. The compact predecessor directly
uses the pinned V6 omitted-c1 grammar. No cache modules were installed or
replayed, and neither the old 448-byte full-message framing nor the old
25-lane / one-root-helper probability is used.

The required fixing order is C1; then lambda and chi; adaptive C2; theta;
ten-coordinate equality point; mu; initial mask claim; nonzero eta; ten
send-then-challenge rounds; and adaptive terminal openings. Row/Poseidon/copy
correspondence, commitment binding, and actual fresh-sampler/ROM conditions
are not proved by changing the order of theorem binders.

No full 310/|K| scalar, source acceptance probability, payment extraction,
or Fiat--Shamir claim is exported. The strongest new quantitative theorem
here is the ideal fixed-plan ten-round repair bound; all other exception
terms and authentication alternatives remain explicit.

## Frozen build evidence

Research checkpoint parent: `125320408ae38060fab9c97391958025d353ce10`.
Inherited runner/cache parent: `289d7356c78a4cd493fe61a54f9548f2a0c11298`;
borrowed V7 pin: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
Root ran each focused target with Lean 4.32.0 `-j1 -M9500` via the numeric
Tailscale endpoint. The cgroup retained MemoryHigh 8 GiB, MemoryMax 10 GiB,
MemorySwapMax 0, and CPU quota 200%. V5 passed both 1,065-entry provenance
checks. The sole local recursion allowance is documented above; heartbeat
and memory caps did not increase.

| Version | Exact tag | Exit | Wall | Peak RSS KiB | Swap |
| --- | --- | ---: | ---: | ---: | ---: |
| V1 (unsuffixed source) | `selected-semantic-terminal-alternative-nuc-v1` | 1 | 11.11 s | 6,679,088 | 0 |
| V2 | `selected-semantic-terminal-alternative-v2-nuc-v1` | 1 | 10.37 s | 6,678,328 | 0 |
| V3 | `selected-semantic-terminal-alternative-v3-nuc-v3` | 1 | 3.07 s | 6,679,168 | 0 |
| V4 | `selected-semantic-terminal-alternative-v4-nuc-v1` | 1 | 3.65 s | 6,679,292 | 0 |
| V5 | `selected-semantic-terminal-alternative-v5-nuc-v1` | 0 | 4.42 s | 6,712,844 | 0 |

V1/V2 exposed arithmetic elaboration timeouts in the Plan-specialized mean,
a numeral normalization, and deep one-run transport. V3 moved the induction
to arbitrary finite bad sets, exposing only a summand-order error and the
core membership application. V4 fixed the arithmetic and isolated that
application, leaving the second transport/linter depth boundary. V5 scopes
depth 400 precisely to `repair_hits_plan`. All seven audited V5 theorems
use only subsets of `propext`, `Classical.choice`, and `Quot.sound`; there are
no `sorryAx` dependencies or compiler warnings in the green log.

| Version | Source/snapshot SHA256 | Log SHA256 | Manifest SHA256 |
| --- | --- | --- | --- |
| V1 | `0b0bbfa14aca40dee820cd54cb04e391832772c805719ac78d3c24a1e972cdd8` | `ab758c1c127b302922131d1d14c8aa282112963cb97320f22ee3542d1a2c8453` | `2635a53dc86027673b56784e3c659dbbc2e39c92a9289a8cce1d5bcc81807628` |
| V2 | `296e583c161c6305c792fa9731a1c8a275c4322aacd9bb94d50073eb8766e02c` | `920c10515e89b0c19a44b51d63150303e175d891da3bc5eb4d79c77ee3a30939` | `eb3f6435d37e8671c4940979aff51c51aa471277467aa01a11be23c6120831f3` |
| V3 | `37dac7fb48c27ac8dcae29409703aab92fd2173f65888fb39ee680deca728a8b` | `34886a999f8bde587eadb466e634fab50422f0b0c4de4fe6221825b3ba11f7be` | `cd4bc0991738796ada755053b78ac396acefb2e60017d1f6099f7f935da72069` |
| V4 | `7463386a70e2658c554c7684161fb68dd99ac732b68fcef05ba473fabbe04cf9` | `8a2b6880a9cf895cc6de327002028acc28a575c315b68d010d7ea99f4ba451cc` | `eba4e59ffc95551e23cd860db8246e36b6802bc3eb1822a2e615a975bfb6eb82` |
| V5 | `1416ad6581d054c76885d2f0942b147c36599a4472013cc7945c4dfb9ba71f48` | `7f56339a43683fd1aca03493ee07e2abb2ac858e21383536a517d7f3c04ddd30` | `fba07d8ca5c51733d204012d361964a35064ee02e84425ad49c9203429c0e5c4` |

Green output SHA256:
`96ce73961826d28805cfd20f86897bd5ee636421203735a33674fae3f1c47744`.
The ignored local olean is hash-checked when present, not required in a clone.
`experiments/audit_selected_semantic_terminal_alternative.py --check-recorded`
validates all five attempts against the immutable receipt
`experiments/selected-semantic-terminal-alternative-evidence.json`, without
running any compiler or touching imported artifacts.
