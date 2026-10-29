# Exact next consumer after runjoin52

Same worktree `/Users/dominic/ZK/.worktrees/pv-runjoin`, branch
`codex/pv-runjoin-20261026`. Entry ef805d853c (LOG D457). All assigned
IDs 65500–65599 are spent on 100 Lean attempts, including audits 65597–65599.
0 Kani. A later run needs a fresh explicitly assigned budget/range.
PV_RJDec_ and all PV_OWN* remain read-only. Step (4) remains prohibited.
No whole ledger row or endpoint premise was removed. Target not established.

1. Finish `CircleInstalled52.complete` first. Its import closure is now
   compatible: attempt 65596 imported the model plus the neutral source without
   the generated-instance collision, but rejected the projection rewrite.
   `PV_B2_F_RawNative.preserved_259` rewrites; the subsequent `candidate`
   rewrite has no matching dictionary projection. Inspect the exact remaining
   dictionary argument with explicit printing, then prove/use named field
   projections. Do not unfold whole dictionaries or raise limits. The current
   candidate and its `candidate` declaration are uncredited as a module.
2. The actual owned callback source side is now checked separately:
   `CircleOwnedSelected52.source` equates the AL-selected op259 with
   `CircleNeutralSelected52.selected` at every block and row. It consumes the
   full source sampler Result law `CircleOwnedComplete52.complete`, its sampler
   and tower laws, and the two fallback branches. These modules import only
   the authoritative owned circle Types side, never R72 Types.
3. The R72 source side is also checked: `CircleR72Ops52.op39` maps the complete
   authoritative secure_ood_circle_point_from_parameter Result into the same
   standard nested-U32-pair/Bool representation. All 41 operation transports
   are checked. Their modules import only the EJR-selected R72 side.
4. **Still open: canonical equality of the neutral computations.** Both raw
   definitions can now be imported together without either colliding generated
   Types module. R72 keeps checked arithmetic and the r23/r24 guards; the owned
   side keeps wrapping/CT arithmetic. Prove equality on the actual sampler's
   produced canonical domain, deriving intermediate canonicality. Do not
   assume the desired full-circle equation, sampler success or stored values.
   `CircleNeutralBase52`, `CircleNeutralScalar52`, `CircleNeutralAdd52` and the
   split `CircleOwnedTower52` aggregation interface are uncompiled drafts,
   explicitly uncredited. The lower-level owned Op0–Op21 transports are checked.
5. Finish the actual original common-sample prepare association, using the
   original toRP completion, retained RAddrIn/RCausal/collision/public-address
   guards, and the actual full producer's framed messages, stored alpha and
   circle fields, coefficient trace, domain/map_err and returned record.
   CommonSemanticSource51's associated input literals are not producer proofs.
6. Then the step-(2) actual backend hinput producer through initialization,
   build_with_material and message-mutating commitments. Derive length 29 and
   canonical coefficient inputs; never assume backend.messages=model messages.
7. Then FinishContext47, both opening constructors/model, 22 query appends,
   six node multiproofs/indices and the complete ordered publication equation.
   No named RUNJOIN_PUBLISH_COMPACT input theorem exists yet for pv-rj4idb.
   Deployed op79/op254 and disclosed/observerOracle installations stay step (4).

Do not co-import the source adapters. Standard-type statements do not erase
transitive imports. The neutral definitions are proof-native reifications,
not substitutions for either pinned generated source. See COLLISION-BRIDGE.md,
audit-design.json and the audit receipts for the separated closures.

The long r24 cell is now fast by eight explicit guard splits and one-bind
transport. Do not return to split_ifs or a whole-cell simp with bind_assoc;
65567/65568 exceeded simplifier steps. 65520 compared inverse functions by
kernel reduction and timed out; 65521 uses funext on the named scalar law.
65555 closed a structured result before unfolding its encoder and exceeded
recursion; the replacement unfolds only that small encoder. All failed source
revisions and original logs are retained. Limits were never raised.

TrustItems, endpoint fields, observer/simulator, coupling/events/guards,
failure independence and side-channel scope remain unchanged. Frozen Rust
and client sources equal 82566acdfb. V370 and D381/D386 remain retained;
no new native or machine-code credit and no full release replay.
