# Admitted full withdrawals cannot pass native compiler preparation

Status: checked mathematical admission (Lean 38144) and checked optimized native rejection (`pv27-zero-change-03`). The 250/750 control succeeds; the 1000/0 case returns `Err(Conservation)`. Final audit is recorded in REPORT.md.

The requested universal coverage is over **every witness/statement of the admitted spend relation**. Take `PV_RunJoin_SpendDomain27.witness` and `.statement`:

- withdrawal variant;
- input value 1000, withdrawal/output value 1000, change value 0;
- the original deterministic fixture input key, salt, pair and 24-level membership path;
- change owner/salt `digest 700` / `digest 800`, with the change commitment computed at value zero;
- the output pair computed from that new change commitment, and a newly computed append root and carry frontier, via `attachAppend` / `seal_append`.

`admitted` proves `BuilderSpendRelation.RspendPlus statement witness`. The proof supplies the complete option shape, input relation, integer conservation, change hash, withdrawal amount and append binding. The transfer-only sentinel implication is vacuous for withdrawal. It neither assumes the conclusion nor modifies the admitted relation.

The native wrapper `compile_pool_v1_pair_forest_withdrawal_merged_c1_v1` rejects `witness.change.value == 0` with `Conservation` before calling `compile_forest_from_copies` (`source-guard.json`). Hence no value-preserving native representation of this witness can return a successful compilation. This impossibility is independent of all digest encodings: the change-value guard rejects every representation that preserves zero, or an earlier check rejects it. The native probe additionally checks the concrete canonical-data instance, with a successful 250/750 withdrawal as a control.

This is a **domain/coverage finding**, not a proof of a privacy distinguisher, a refutation of the accepted V152–V154 honest-family certificate, or an arbitrary corrupted cached-payload example. It refutes total successful preparation for the admitted relation requested here. It does **not** refute the narrower statement “if preparation successfully returns, its output satisfies HonestInput”; that separate successful-output implication remains unproved.

For an owner decision, the present native route requires a positive-change honest-user domain. Full withdrawals are members of the stated admitted relation but cannot be prepared by that route. Adopting a narrower advertised domain, or changing the frozen compiler to support zero change, requires an explicit owner decision and its corresponding proof/release work. No such change is made here.
