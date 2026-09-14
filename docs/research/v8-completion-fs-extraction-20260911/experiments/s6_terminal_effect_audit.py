#!/usr/bin/env python3
"""Narrow, reproducible source audit for the S6 terminal-guard cut.

This is deliberately a static source test, not a Rust refinement theorem.  It
checks the direct selected `payment_terminal` call site and the selected
generated terminal module for the shared SHA transcript API.  A passing result
means only that the inspected source does not lexically invoke that API on the
selected terminal path; it does not prove payment correctness, absence of all
effects, or correspondence to Lean.
"""

from __future__ import annotations

import hashlib
import json
import pathlib
import re
import sys


ROOT = pathlib.Path(__file__).resolve().parents[4]
PERFORMANCE = ROOT / "docs/research/v8-no-work-100-20260907/experiments/performance_verifier.rs"
TERMINAL = ROOT / "crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs"
SELECTED_CALLBACKS = ROOT / "docs/research/v8-completion-fs-extraction-20260911/lean/FSV8S5SelectedVerifierCallbacks.lean"


def source_hash(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def function_body(text: str, name: str) -> str:
    match = re.search(r"(?:pub\(super\)\s+)?fn\s+" + re.escape(name) + r"\b", text)
    if match is None:
        raise AssertionError(f"missing function {name}")
    start = text.find("{", match.end())
    if start < 0:
        raise AssertionError(f"missing body for {name}")
    depth = 0
    for index in range(start, len(text)):
        if text[index] == "{":
            depth += 1
        elif text[index] == "}":
            depth -= 1
            if depth == 0:
                return text[start : index + 1]
    raise AssertionError(f"unclosed body for {name}")


def main() -> None:
    performance = PERFORMANCE.read_text()
    terminal = TERMINAL.read_text()
    callbacks = SELECTED_CALLBACKS.read_text()
    body = function_body(performance, "payment_terminal")
    forbidden_direct = ("Transcript", "sha2", "HashFn", "hash(", "solana_program")
    hits = [token for token in forbidden_direct if token in body]
    if hits:
        raise AssertionError(f"shared-oracle token(s) in payment_terminal: {hits}")
    required = (
        "evaluate_pool_v1_pair_forest_private_transfer_selected_masked_terminal_compiled_tag73_v1",
        "evaluate_pool_v1_pair_forest_withdrawal_selected_masked_terminal_compiled_tag73_v1",
        "state_only_selected_mask_value",
    )
    missing = [token for token in required if token not in (body + terminal)]
    if missing:
        raise AssertionError(f"selected terminal route missing: {missing}")
    terminal_imports = terminal.split("\n\n", 1)[0]
    forbidden_imports = ("sha2", "Transcript", "HashFn")
    import_hits = [token for token in forbidden_imports if token in terminal_imports]
    if import_hits:
        raise AssertionError(f"shared SHA import in generated terminal module: {import_hits}")
    # This is intentionally a *negative* closure test.  The current selected
    # configuration uses read-only placeholders and therefore cannot be named
    # as the literal selected OOD/source producer in an endpoint theorem.
    if "def readOnlyFirst (_ : Point) : Script Bytes HB Unit 0 := .done ()" not in callbacks:
        raise AssertionError("S5 callback model changed; re-audit source binding")
    if "def readOnlySecond (_ _ : Point) : Script Bytes HB Unit 0 := .done ()" not in callbacks:
        raise AssertionError("S5 callback model changed; re-audit source binding")
    print(json.dumps({
        "scope": "static selected-terminal shared-SHA audit; not refinement",
        "performance_verifier_sha256": source_hash(PERFORMANCE),
        "pair_forest_terminal_sha256": source_hash(TERMINAL),
        "payment_terminal_direct_shared_sha_tokens": hits,
        "generated_terminal_module_shared_sha_import_tokens": import_hits,
        "selected_configuration_uses_literal_ood_source_producer": False,
        "result": "PASS",
    }, sort_keys=True))


if __name__ == "__main__":
    main()
