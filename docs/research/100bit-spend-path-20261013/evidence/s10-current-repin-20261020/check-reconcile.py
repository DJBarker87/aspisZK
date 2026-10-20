#!/usr/bin/env python3
"""Retained generated identity must not erase missing Rust correspondence."""
from pathlib import Path
import importlib.util
root = Path(__file__).resolve().parents[5]
path = root / "docs/research/100bit-spend-path-20261013/tools/j1-integrated-declaration-repin.py"
spec = importlib.util.spec_from_file_location("repin", path)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
emitted = {"lean_name": "same", "body_sha256": "body", "signature_sha256": "sig", "signature": "def same"}
for status in ("unresolved", "re-extracted"):
    rows = [{"cone": "prior", "retained_signature": {"generated": [emitted]}},
            {"cone": "followup", "classification": status, "retained_signature": {"generated": [emitted]}}]
    if status != "unresolved":
        rows[1]["identity_basis"] = "Rust correspondence verified."
    m.reconcile_followup_statements(rows, [], {"followup"})
    assert rows[1]["classification"] == ("unresolved" if status == "unresolved" else "unchanged")
    assert rows[1]["prior_current_emission_comparison"][0]["body_status"] == "identical"
    if status == "unresolved":
        assert "unresolved Rust" in rows[1]["generated_diff_status"]
print("PASS: unresolved Rust correspondence preserved; verified source identity still reconciles")
