# Proposed ARX statement amendment — 27 October 2026

**DRAFT ONLY — not approved, adopted, or applied to the security contract.**

This text describes the definition choice the owner would approve. The
authoritative contract and premise ledger remain unchanged. ARX is a proved
candidate; the deployed 100-bit release target is not yet established.

## Proposed statement change

Use `AspisR1.ARX_Root.deployed` as the admitted-game candidate statement in
place of the independently supplied `P`, `runtime`, and `binding` interface
of `AspisR1.Rc10_Top.deployed`. The change is precisely:

```lean
-- Before
(P : F3T_ByteCarrier.ByteProver) (Q0 Q1 : Nat)
(queries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q0+Q1)
(runtime : F3T_Runtime.Runtime)
(binding : F3T_Runtime.StoredCarrierBinding
  (FIp_Install.configuration indexError c reservation) D
  (F3T_Installed.source
    (FIp_Install.configuration indexError c reservation) hashv) P runtime)

-- Proposed after
(a : SCE_Experiment.Adversary A) (Q0 Q1 : Nat)
(queries : ∀ H : Bytes → State,
  (ARW_Induced.issued native1 copy allocator CPH_Program.verifier a H).length
    ≤ Q0+Q1)
-- In the conclusion:
let P := ARW_Induced.program native1 copy allocator CPH_Program.verifier a
let runtime := ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator
  c indexError reservation native1 native2 hashv a
```

These are signature excerpts, not a new Lean theorem. The complete kernel
statements and exhaustive binder diff are in
`evidence/recount11-20261027/Rc11_BEFORE.lean.txt`,
`Rc11_AFTER.lean.txt`, and `Rc11_statement.diff`.
All other binders remain unchanged, including extraction, SDK/std, runtime
admissions, native success antecedents, fixed native pair, the game,
RuntimePersistence and the native/global finish obligations. No new
propositional premise is introduced. This is not an assertion that the
removed `StoredCarrierBinding` holds or that the new theorem is obtained
by directly applying Rc10 to its defined runtime.

## Issued queries and adversary

The adversary is arbitrary and fixed before the oracle world. Its first
program chooses the original account inputs. Its second program may depend
on the first inputs, actual saved checkpoint, post heap and allocator state,
as well as its own oracle responses. No pure-second-choice restriction is
introduced.

For each H, define the adversary's issued query list as
`ARW_Induced.issued native1 copy allocator CPH_Program.verifier a H`:
the first phase's chronological list followed, when the native first wrapper
succeeds, by the reached adaptive second phase's chronological list.
Duplicates and reached rejecting prefixes count as issued work. `Q = Q0+Q1`
is a uniform upper bound on this length, not an equality on every path.
`ARW_Induced.queries` identifies this exactly with `(eval H P).1.length`.
Thus L154 remains the same external P budget condition at induced P; the
definition supplies no free concrete workload budget. The verifier's query
overheads remain separately charged below.

On admitted worlds, `ARX_LawEquivalence.work` identifies this induced work
with the full account experiment's adversary work. The full observer's
ordered log is retained on every world, including outside admission
(`ARX_RejectedPrefixes.cost`); source rejections contribute zero failure
mass (`ARX_RejectedPrefixes.mass`). No discarded attempted query is given
free work.

## Admitted runtime image and outcome law

Interpret the runtime in the security functional as the semantic observer
`ARX_AdmittedRuntime.runtime`, not an independent arbitrary runtime and not
the unrestricted ART runtime. This is a noncomputable mathematical observer;
it changes no deployed source or bank admission implementation.

A completed account cylinder is in its image exactly when it possesses its
own `ARU_Support.At` witness: its own entries, native saved/post/final tuple,
both runtime admissions and native successes, bank observations and
two-transaction game a–d, RuntimePersistence, and agreement at the issued
first/second source digest addresses. These are membership data inside the
observer, not an assumed all-world admission law. A fixed unrelated native
tuple at the root cannot manufacture admission for every adversary.
`ARX_Domain.range` checks this exact range after the retained extraction
boundary is supplied.

For an actual native execution with its own SupportedEntry and successful
syscall interpretation, every oracle world consistent on that execution's
queried cylinder has the same complete evaluation
(`ARX_Coverage.coverage`). Worlds with different queried answers describe
different executions. No global native-hash/random-oracle equality is added
to this coverage theorem.

The separate fixed native tuple in the root still has its original
`p1 : S2W_ExtractionBoundary.P1 sha256 H`; unfolding its realization field
gives `∀ bytes, sha256 bytes = H bytes`. This unchanged L081 trust boundary
is distinct from query-restricted coverage across a cylinder. This draft
does not remove it or claim that its kernel definition is query-restricted.

On admitted worlds the observer returns the original complete RunView and
original query log. `ARX_Carrier.exact` identifies its proof/public bytes with
the induced account submission and its resumed checkpoint with the SAME
saved vector from the returned source cuts. Carrier types, extraction and
checkpoint byte meaning are unchanged. Outside the admitted image it
returns None, retaining the original issued log.

The security mean is zero-extended outside the admitted image using the
original oracle weights. It is **not** a conditional distribution and is
never divided by the probability of admission. The scan-failure term is
added once as before. `ARX_LawEquivalence.mean/failure_mean` state this
precisely. No equality with the global unrestricted ART mean is approved by
this amendment. `ARX_OldClassPoison.differs` checks that even the old
pure-second-choice class can distinguish the observers. The accepted
unsupported poison class is excluded by the inherited no-admission proof,
not by assuming adversaries avoid it.

## Unchanged security target, bound and margin

The 100-bit classical per-attempt target, adopted frozen3 model, failure
mass/extractor definitions, physical public/proof/checkpoint carriers,
collision-event constructor, work metric and all trust items remain.
This draft authorizes the admitted-image argument of that existing failure
functional; it does not assert literal equality with its value at arbitrary
independent runtimes. The account event remains the exact
`BinRawByteCollisionTargets.event` on the complete account recorder at
`Q+2965`, instantiated at the induced P.

The unchanged numeric upper bound is `F3T_Numeric.total Q`:

```text
(Q+34)·PerAttemptEnvelope.B
  + 6·(Q+1161)^2 / 2^256
  + 6·(Q+2965)^2 / 2^256
  + 2^-126 + 2^-454.
```

The Q+34 starts, Q+1161 distinct reads, Q+2322 issued calls and Q+2965
account charge are unchanged (`ARX_LawConstants.unchanged`). The existing
range remains `Q ≤ F3U_RangeEdges.maxQueries`, exactly
`7388980242446479800895501321004157112314840375`, for the bound
`(Q+1)·2^-100`. At Q=0, the unchanged exact positive spare margin is

```text
2^-108 − 6·(1161^2 + 2965^2)/2^256 − 2^-126 − 2^-454 > 0.
```

No grinding credit, query loss, abort term, numerical constant or target is
changed. The raw source conclusion from `let select` onward is identical;
the closed proposition is specialized through the defined P and runtime.

## Adoption scope and outstanding obligations

If approved, the statement change removes L159 and its deployment alias
L185, plus L181's admitted experiment/native-prefix query association. It
does not close L166's native/source Result and ordered effects fidelity,
L187's coherent frozen dependency replay or L188's final artifact/trust and
dependency audit. L181 credit is not source-to-ELF correspondence.

Proposed distinct totals: actual antecedents 83T/12P/13G/0C to
83T/11P/13G/0C; deployment-inclusive 89T/16P/13G/0C to
89T/14P/13G/0C. The new adversary and defined-P/runtime data introduce no
atomic T/P/G/C premise. All ten native/global finish P families and the
external L154 query budget remain. Until adoption, the actual Rc10 totals
and authoritative ledger remain unchanged.

`ARX_Nonvacuity.conditional` still requires the complete SAME installed
accepted real-byte native pair and consistent cylinder; the partial fixture
predecessors listed in ARX_ROOT_COMPARISON do not construct that pair or
jointly inhabit all release hypotheses. This amendment would not approve
a completed implementation-release claim.

No source, artifact or new trust item is adopted by this draft. Inherited
ELF pins (not fresh rebuild evidence) remain:

- default: `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`
- devnet: `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`
- Pool: `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`
