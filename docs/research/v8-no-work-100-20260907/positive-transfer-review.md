# Opt-in positive-transfer semantic integration

Source checkpoint: `33e13de4e4b8bfdef7f3f2fb2e472b34db44865e`.
This is a **new, transfer-only research profile**, enabled solely by
`--cfg v8_positive_transfer`. The selected default, production crates, main,
deployment configuration and measured complete-transaction build are unchanged.

## Executed result

The proposed inverse-product equation is now inside the actual research
semantic terminal and producer, not a standalone check after acceptance.
One genuine compiled, masked transfer produced a complete q22 proof and
passed the public-input research verifier (including the carried image and
shifted ordinary/query relations). Its body is **38,982 bytes**. The protocol
maximum is still **40,282 bytes**, not the size of this particular schedule.

Both predeclared zero-output controls were rejected at the actual verifier's
semantic error `4`, after parsing and ten compact semantic responses. They
have actual fixed C1/C2 roots and genuine masks/helpers, not opaque semantic
prefixes. Their later PCS suffix was deliberately left unconstructed: the
test establishes rejection at that earlier boundary, **not a complete
negative PCS proof or a universal rejection theorem**.

Each case uses seed1 exactly once. No nonce scan, challenge forcing, retry or
favourable transcript selection ran. Legitimate exceptional challenges are
not excluded by the design: the negative fixture would record a failed test,
not retry, if its initial discrepancy happened to cancel.

| Executed case | Result | Wall seconds | Peak RSS bytes | Swap |
|---|---|---:|---:|---:|
| Optimized cfg-specific host build | Exit0 | 44.99 | 808,206,336 | 0 |
| Positive 600/400 transfer | Full research proof accepted; existing malformed controls reject | 7.21 | 218,103,808 | 0 |
| Recipient0/change1000 | Semantic verifier rejection | 6.84 | 217,268,224 | 0 |
| Recipient1000/change0 | Semantic verifier rejection | 6.90 | 217,071,616 | 0 |

The positive run measured 5.651607041 seconds for proving excluding setup,
with 1.189731166 seconds for the compiler/encoder/quotient-decoder matrix setup.
These are one Apple aarch64 host execution, not the earlier NUC benchmark,
mean/tail latency, replay-extractor time or CU. No SBF build ran.

## Exact semantic change

The new local equation at row1014 is

```
z[1] * successor(z)[1] * z[3] - 1 = 0.
```

The first two cells already contain linked recipient/change values. Existing
cell `(1014,3)` carries their product's inverse; no new copy edge is needed.
`SelectedTransferPositive.selected_strict_amounts` already proves positivity,
range and exact conservation from this residual and the selected range/copy
equations. It does not assume successful decoding or compiler acceptance.

The source has 94 existing semantic source lanes, packed into24 QM31 lanes
after four Poseidon lanes. New source lane94 occupies packed group23, limb2.
Its delta in the theta composition is exactly

```
theta^27 * pack(0, 0, selector1014(z) * residual, 0).
```

The masked terminal adds `eta * equality(zc,z) * delta`; H/G mask terms,
copy terms and all existing semantic terms remain present. Packing is the
source's actual extension-linear `qm31_pack_base4`, not a base-field cast of
an arbitrary QM31 residual. Thirty-two arbitrary-QM31 controls, including
zero theta, compare this delta with the literal 29-lane Horner assembly.
`PositiveTerminalInsertion.positive_terminal_insertion` additionally proves
the signed-limb field packing, reverse-Horner ordering, theta27 preparation
and full additive masked-terminal identity. It reuses V7's packing-linearity
theorem for arbitrary extension inputs. This is kernel-checked source-shaped
field algebra, not a translated Rust integer/canonical-parser proof. The
base expression uses this same repaired execution's current claims and mask
values; it does not assert unchanged proof bytes across the new profile.

The individual-degree allowance does not increase: each coordinate of the
successor map is multilinear, so a 10-variable MLE composed with it has
individual degree at most10. The two ordinary MLE factors, row selector and
equality factor add at most4, giving an upper bound14 for the added term,
below the retained masked degree27. This degree argument remains an explicit
algebra/source proof obligation; the existing ten degree27 responses are not
enlarged on the strength of tests alone.

## Masking and timing

The adapter retains the legacy mask generator, its 3,803 draws and its exact
draw order, mask-only C1, G, D and H padding. After the source applies masks
and balances each semantic column, the adapter overwrites the **active**
cell `(1014,3)` with the inverse, before encoding or committing C1.

This discards one old independent draw; it does not silently pretend the
legacy generator sampled a new list of 3,802 cells. Source checks establish
that the balancing dependent remains row1023 for all16 columns. All other
cells remain identical to the old masked table, all canonicality checks
pass, decoded witness fields remain identical and all16 inactive sums remain
zero. The fixed positive table passes `extract_checked` using independently
provisioned synthetic runtime context. This call is **given the table**;
this run adds no authenticated-opening or replay extraction stage.

The new [mask adapter theorem](selected-transfer-mask-review.md) formalizes
the additions, balancing overwrites and active-cell restoration. Its field
projection theorem does not replace the decoder's global canonicality scan.

The old mask inventory fingerprint is `f9daf3d54f4285d1`; the remaining
inventory fingerprint is `6b661245a56c7189`. A canonical107-byte,
verifier-derived description binds the parent profile, adapter version,
cell, lane, both inventories and the new count. It is absorbed **before C1
and lambda/chi**. Its full bytes determine the semantics; the FNV inventory
fingerprints are not treated as cryptographic assumptions or prover claims.
Mask entropy also receives a separate profile-derived precommit binding;
the legacy context fingerprint still truthfully names the retained generator.
The binding is not removed or replaced by an unchecked prover-supplied hash.

## Cost and privacy boundaries

```
697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282 bytes.
```

No new transmitted claim, nonce, root, query, final coefficient or round is
added. The existing three work/nonce records remain in the body and can
affect selection; they earn **zero** security credit.

The present additive reference wrapper performs **39 QM31 multiplications,
four QM31 squarings and one packed-field operation** per terminal call.
This includes rebuilding row/equality selectors and theta powers already
available inside the selected terminal; it is not the smaller hypothetical
cost of an integrated lane. The prover adds one M31 product/inversion and
discards one mask draw. Descriptor construction currently enumerates the
fixed mask layout; that is real reference work, not a frozen-cost SBF kernel.
The extra verifier absorb hashes141 input bytes (34-byte framing plus107-byte
description), requiring three SHA-256 compression blocks including padding.
There is one additional profile-binding hash in honest entropy preparation.
No CU saving or parity is assigned to these operation counts.

Removing one mask generator and constraining its old cell changes the joint
witness-dependent distribution. The previous q16 rank gates do not cover this
q22/two-OOD/cubic-response/image view. The precise next privacy probes and
their limitations are identified in the mask report. Full-view adaptive
simulation remains required; neither field-read invariance nor positive
rank at fixed challenges establishes it.

The positivity profile intentionally rejects withdrawals and refuses the
complete-transaction context mode. It is not selected by the complete pool
wrapper or its published CU evidence. Extension to withdrawal is a distinct
semantics obligation, not inferred from the transfer case.

## Evidence and next decision

`run_positive_transfer.sh build NEW_LOG` creates a bounded optimized offline
host build and records its exact source manifest. Then run `honest`,
`recipient_zero`, and `change_zero` with fresh logs and that build directory.
All jobs used a7-GiB aggregate-RSS guard and zero swap. Successful logs are in
`evidence/positive-transfer-*-v1.log`; artifact hashes and exact ledger are in
the accompanying continuation evidence. No raw witness or mask is logged.

**Decision:** retain this as an opt-in research control. It supplies an actual
semantic repair path for the demonstrated strict-endpoint mismatch. It is
not ready to replace the CU-tested profile until the changed full-view
masking argument and matched complete-transaction costs are justified. The
decisive next repair gate is the actual q22 disclosure/mask-image test, followed
by a symbolic simulator argument if it survives; global accepted C1 recovery
and source/FS coupling continue independently.
