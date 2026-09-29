#!/usr/bin/env python3
"""Stage the exact old callback graph against the current R28/R26 types.

The five callbacks used by the R28 production observer have unchanged source
bodies relative to the axiom-clean August 30 extraction (the openings helper's
current source only adds a cfg branch which is disabled by the R28 feature
set).  This script reuses that checked generated graph, gives it a fresh
namespace, and aliases shared values to the R28/R26 graph so the definitions
can discharge R28's callback externals definitionally.

The script intentionally performs only exact, counted substitutions.  It
refuses a changed input graph and checks the aggregate SHA-256 of every staged
Lean source before returning.
"""

from __future__ import annotations

import argparse
import hashlib
import shutil
from pathlib import Path


OLD_NAMESPACE = "V7Tag73CurrentHelpersOpaque"
NEW_NAMESPACE = "V7ProductionCallbacksR29"
EXPECTED_LEAN_FILES = 142
EXPECTED_AGGREGATE = (
    "52993aea25dfa41d1e0f222726e5ed2da6f98b665b835708d19588edfd5d6465"
)


def replace_exact(text: str, old: str, new: str, count: int = 1) -> str:
    actual = text.count(old)
    if actual != count:
        raise RuntimeError(
            f"expected {count} occurrence(s), found {actual}: {old[:100]!r}"
        )
    return text.replace(old, new)


def rewrite(path: Path, transform) -> None:
    original = path.read_text()
    updated = transform(original)
    if updated == original:
        raise RuntimeError(f"rewrite made no change: {path}")
    path.write_text(updated)


def stage_tree(source_root: Path, output_root: Path) -> None:
    if output_root.exists():
        raise RuntimeError(f"refusing to reuse output directory: {output_root}")

    old = source_root / "V7Tag73CurrentHelpersOpaque"
    gamma = source_root / "V7GammaSlotMajorLiteral"
    dot3 = source_root / "V7Qm31Dot3Reduced"
    for required in (old, gamma, dot3):
        if not required.is_dir():
            raise RuntimeError(f"missing checked source directory: {required}")

    output_root.mkdir(parents=True)
    callback = output_root / NEW_NAMESPACE
    shutil.copytree(old, callback)
    shutil.copytree(gamma, output_root / gamma.name)
    shutil.copytree(dot3, output_root / dot3.name)

    # Namespace only Lean sources.  Historical chunk manifests are evidence
    # for the original split and deliberately retain their original caller.
    namespace_occurrences = 0
    for path in callback.glob("*.lean"):
        text = path.read_text()
        count = text.count(OLD_NAMESPACE)
        if count:
            path.write_text(text.replace(OLD_NAMESPACE, NEW_NAMESPACE))
            namespace_occurrences += count
    if namespace_occurrences != 472:
        raise RuntimeError(
            f"expected 472 namespace occurrences, found {namespace_occurrences}"
        )


def alias_shared_types(callback: Path) -> None:
    types = callback / "Types.lean"

    def transform(text: str) -> str:
        text = replace_exact(
            text,
            f"import {NEW_NAMESPACE}.TypesExternal\n",
            f"import {NEW_NAMESPACE}.TypesExternal\n"
            "import V7ProductionSnapshotObserverR28.Types\n",
        )
        replacements = [
            (
                '@[reducible, rust_type "aspis_core::field::M31"]\n'
                "def aspis_core.field.M31 := Std.U32",
                '@[rust_type "aspis_core::field::M31"]\n'
                "abbrev aspis_core.field.M31 := "
                "V7ProductionSnapshotObserverR28.aspis_core.field.M31",
            ),
            (
                '@[rust_type "aspis_core::field::CM31"]\n'
                "structure aspis_core.field.CM31 where\n"
                "  a : aspis_core.field.M31\n"
                "  b : aspis_core.field.M31",
                '@[rust_type "aspis_core::field::CM31"]\n'
                "abbrev aspis_core.field.CM31 := "
                "V7ProductionSnapshotObserverR28.aspis_core.field.CM31",
            ),
            (
                '@[rust_type "aspis_core::field::QM31"]\n'
                "structure aspis_core.field.QM31 where\n"
                "  c0 : aspis_core.field.CM31\n"
                "  c1 : aspis_core.field.CM31",
                '@[rust_type "aspis_core::field::QM31"]\n'
                "abbrev aspis_core.field.QM31 := "
                "V7ProductionSnapshotObserverR28.aspis_core.field.QM31",
            ),
            (
                '@[rust_type "aspis_core::field::PreparedQm31Multiplier"]\n'
                "structure aspis_core.field.PreparedQm31Multiplier where\n"
                "  components : Array (Array aspis_core.field.M31 3#usize) 3#usize",
                '@[rust_type "aspis_core::field::PreparedQm31Multiplier"]\n'
                "abbrev aspis_core.field.PreparedQm31Multiplier := "
                "V7CallerCurrentReleaseR26.field.PreparedQm31Multiplier",
            ),
            (
                '@[rust_type "aspis_core::state_only_hiding::StateOnlyHidingContext"]\n'
                "structure aspis_core.state_only_hiding.StateOnlyHidingContext where\n"
                "  statement_digest : Array Std.U8 32#usize\n"
                "  mask_nonce : Array Std.U8 32#usize\n"
                "  mask_layout_fingerprint : Std.U64\n"
                "  layout_factor_fingerprint : Std.U64",
                '@[rust_type "aspis_core::state_only_hiding::StateOnlyHidingContext"]\n'
                "abbrev aspis_core.state_only_hiding.StateOnlyHidingContext := "
                "V7ProductionSnapshotObserverR28.aspis_core.state_only_hiding.StateOnlyHidingContext",
            ),
            (
                '@[rust_type "aspis_core::state_only_query::StateOnlyQueryPowers"]\n'
                "structure aspis_core.state_only_query.StateOnlyQueryPowers where\n"
                "  c1_limbs : Array (Array Std.U32 4#usize) 26#usize\n"
                "  helpers : Array aspis_core.field.PreparedQm31Multiplier 2#usize",
                '@[rust_type "aspis_core::state_only_query::StateOnlyQueryPowers"]\n'
                "abbrev aspis_core.state_only_query.StateOnlyQueryPowers := "
                "V7ProductionSnapshotObserverR28.aspis_core.state_only_query.StateOnlyQueryPowers",
            ),
            (
                '@[rust_type "aspis_core::state_only_spend_query::StateOnlySpendQueryPowers"]\n'
                "structure aspis_core.state_only_spend_query.StateOnlySpendQueryPowers where\n"
                "  base : aspis_core.state_only_query.StateOnlyQueryPowers\n"
                "  d : aspis_core.field.PreparedQm31Multiplier",
                '@[rust_type "aspis_core::state_only_spend_query::StateOnlySpendQueryPowers"]\n'
                "abbrev aspis_core.state_only_spend_query.StateOnlySpendQueryPowers := "
                "V7ProductionSnapshotObserverR28.aspis_core.state_only_spend_query.StateOnlySpendQueryPowers",
            ),
            (
                '@[rust_type "aspis_core::statement_sumcheck::PaymentConstraintChallenges"]\n'
                "structure aspis_core.statement_sumcheck.PaymentConstraintChallenges where\n"
                "  theta : aspis_core.field.QM31\n"
                "  zerocheck_point : Array aspis_core.field.QM31 10#usize\n"
                "  mu : aspis_core.field.QM31",
                '@[rust_type "aspis_core::statement_sumcheck::PaymentConstraintChallenges"]\n'
                "abbrev aspis_core.statement_sumcheck.PaymentConstraintChallenges := "
                "V7ProductionSnapshotObserverR28.aspis_core.statement_sumcheck.PaymentConstraintChallenges",
            ),
            (
                '@[discriminant isize, rust_type "aspis_core::v6_onefold::V6WireError"]\n'
                "inductive aspis_core.v6_onefold.V6WireError where\n"
                "| FrontierTooLarge : aspis_core.v6_onefold.V6WireError\n"
                "| WrongLength : aspis_core.v6_onefold.V6WireError\n"
                "| NonCanonicalM31 : aspis_core.v6_onefold.V6WireError\n"
                "| InvalidQuerySchedule : aspis_core.v6_onefold.V6WireError\n"
                "| MerkleMismatch : aspis_core.v6_onefold.V6WireError\n"
                "| FriMismatch : aspis_core.v6_onefold.V6WireError",
                '@[rust_type "aspis_core::v6_onefold::V6WireError"]\n'
                "abbrev aspis_core.v6_onefold.V6WireError := "
                "V7ProductionSnapshotObserverR28.aspis_core.v6_onefold.V6WireError",
            ),
            (
                '@[rust_type "aspis_core::v6_onefold::V6OneFoldCoordinates"]\n'
                "structure aspis_core.v6_onefold.V6OneFoldCoordinates where\n"
                "  inv_2x : Array aspis_core.field.M31 16#usize\n"
                "  inv_2y : Array aspis_core.field.M31 16#usize\n"
                "  line_x : Array aspis_core.field.M31 16#usize",
                '@[rust_type "aspis_core::v6_onefold::V6OneFoldCoordinates"]\n'
                "abbrev aspis_core.v6_onefold.V6OneFoldCoordinates := "
                "V7ProductionSnapshotObserverR28.aspis_core.v6_onefold.V6OneFoldCoordinates",
            ),
            (
                '@[rust_type "aspis_core::v7_onefold::V7CompactOneFoldWire"]\n'
                "structure aspis_core.v7_onefold.V7CompactOneFoldWire where\n"
                "  fixed_fields_packed : Slice Std.U8\n"
                "  c1_root : Array Std.U8 26#usize\n"
                "  c2_root : Array Std.U8 26#usize\n"
                "  work_nonces : Array Std.U8 24#usize\n"
                "  query_section : Slice Std.U8\n"
                "  c1_frontier : Slice Std.U8\n"
                "  c2_frontier : Slice Std.U8",
                '@[rust_type "aspis_core::v7_onefold::V7CompactOneFoldWire"]\n'
                "abbrev aspis_core.v7_onefold.V7CompactOneFoldWire := "
                "V7CallerCurrentReleaseR26.v7_onefold.V7CompactOneFoldWire",
            ),
            (
                '@[rust_type "aspis_statement::spend::SpendPublic"]\n'
                "structure aspis_statement.spend.SpendPublic where\n"
                "  anchor : Array aspis_core.field.M31 8#usize\n"
                "  nullifier : Array aspis_core.field.M31 8#usize\n"
                "  output_commitment : Array aspis_core.field.M31 8#usize\n"
                "  asset_id : aspis_core.field.M31\n"
                "  fee : Std.U32",
                '@[rust_type "aspis_statement::spend::SpendPublic"]\n'
                "abbrev aspis_statement.spend.SpendPublic := "
                "V7ProductionSnapshotObserverR28.aspis_statement.spend.SpendPublic",
            ),
            (
                '@[rust_type "aspis_statement::atomic_statement::AtomicPaymentStatementV4"]\n'
                "structure aspis_statement.atomic_statement.AtomicPaymentStatementV4 where\n"
                "  pool : Array Std.U8 32#usize\n"
                "  sequence : Std.U64\n"
                "  spend : aspis_statement.spend.SpendPublic\n"
                "  output_anchor : Array aspis_core.field.M31 8#usize\n"
                "  deployment_domain : Array Std.U8 32#usize",
                '@[rust_type "aspis_statement::atomic_statement::AtomicPaymentStatementV4"]\n'
                "abbrev aspis_statement.atomic_statement.AtomicPaymentStatementV4 := "
                "V7ProductionSnapshotObserverR28.aspis_statement.atomic_statement.AtomicPaymentStatementV4",
            ),
            (
                '@[discriminant isize, rust_type\n'
                '  "aspis_statement::state_only_terminal::StateOnlyTerminalError"]\n'
                "inductive aspis_statement.state_only_terminal.StateOnlyTerminalError where\n"
                "| PublicFeeOutOfRange :\n"
                "  aspis_statement.state_only_terminal.StateOnlyTerminalError",
                '@[rust_type "aspis_statement::state_only_terminal::StateOnlyTerminalError"]\n'
                "abbrev aspis_statement.state_only_terminal.StateOnlyTerminalError := "
                "V7ProductionSnapshotObserverR28.aspis_statement.state_only_terminal.StateOnlyTerminalError",
            ),
        ]
        for old, new in replacements:
            text = replace_exact(text, old, new)
        return text

    rewrite(types, transform)


def wire_existing_externals(output_root: Path) -> None:
    callback = output_root / NEW_NAMESPACE
    (callback / "TypesExternalBase.lean").write_text(
        "import V7CallerCurrentReleaseR26.TypesExternal\n"
    )
    (callback / "FunsExternalBase.lean").write_text(
        "import V7CallerCurrentReleaseR26.Funs\n"
    )

    rewrite(
        callback / "FunsExternal.lean",
        lambda text: replace_exact(
            text,
            f"import {NEW_NAMESPACE}.FunsExternalBase\n",
            f"import {NEW_NAMESPACE}.Types\n"
            f"import {NEW_NAMESPACE}.FunsExternalBase\n",
        ),
    )
    rewrite(
        output_root / "V7GammaSlotMajorLiteral" / "Funs.lean",
        lambda text: replace_exact(
            text,
            "import V7GammaSlotMajorLiteral.MutableIteratorCompat",
            "import V7CallerCurrentReleaseR26.Funs",
        ),
    )
    rewrite(
        output_root / "V7Qm31Dot3Reduced" / "TypesExternal.lean",
        lambda text: replace_exact(
            text,
            f"import {OLD_NAMESPACE}.TypesExternalBase",
            "import V7CallerCurrentReleaseR26.TypesExternal",
        ),
    )
    rewrite(
        output_root / "V7Qm31Dot3Reduced" / "FunsExternal.lean",
        lambda text: replace_exact(
            text,
            f"import {OLD_NAMESPACE}.FunsExternalBase",
            "import V7CallerCurrentReleaseR26.Funs",
        ),
    )


def qualify_shared_constructors(callback: Path) -> None:
    wire_old = "aspis_core.v6_onefold.V6WireError."
    wire_new = "V7CallerCurrentReleaseR26.v6_onefold.V6WireError."
    changed = 0
    for path in callback.glob("FunsChunk*.lean"):
        text = path.read_text()
        count = text.count(wire_old)
        if count:
            path.write_text(text.replace(wire_old, wire_new))
            changed += count
    if changed != 43:
        raise RuntimeError(f"expected 43 V6WireError constructors, found {changed}")

    terminal = callback / "FunsChunk43.lean"
    rewrite(
        terminal,
        lambda text: replace_exact(
            text,
            "aspis_statement.state_only_terminal.StateOnlyTerminalError.PublicFeeOutOfRange",
            "V7ProductionSnapshotObserverR28.aspis_statement.state_only_terminal."
            "StateOnlyTerminalError.PublicFeeOutOfRange",
        ),
    )


def aggregate_lean_sources(output_root: Path) -> tuple[int, str]:
    rows = []
    for path in sorted(output_root.rglob("*.lean")):
        relative = path.relative_to(output_root).as_posix()
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        rows.append(f"{digest}  {relative}\n")
    return len(rows), hashlib.sha256("".join(rows).encode()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("source_root", type=Path)
    parser.add_argument("output_root", type=Path)
    args = parser.parse_args()

    stage_tree(args.source_root.resolve(), args.output_root.resolve())
    callback = args.output_root.resolve() / NEW_NAMESPACE
    alias_shared_types(callback)
    wire_existing_externals(args.output_root.resolve())
    qualify_shared_constructors(callback)

    count, digest = aggregate_lean_sources(args.output_root.resolve())
    if count != EXPECTED_LEAN_FILES:
        raise RuntimeError(f"expected {EXPECTED_LEAN_FILES} Lean files, found {count}")
    if digest != EXPECTED_AGGREGATE:
        raise RuntimeError(
            f"staged source aggregate mismatch: expected {EXPECTED_AGGREGATE}, got {digest}"
        )
    print(f"staged {count} Lean sources; aggregate sha256={digest}")


if __name__ == "__main__":
    main()
