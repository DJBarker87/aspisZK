#!/usr/bin/env python3
"""Clone-portable audit of the fixed-early-C1 higher-Y checkpoint."""

from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re


EX = Path(__file__).resolve().parent
RD = EX.parent


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    source = EX / "EarlyC1HigherYSupport.lean"
    assert sha(source) == "621ad297e6b7248cc40f6da0060db205e01f0977fb97c46882794f01f055f64a"
    assert source.read_text().count("#print axioms ") == 7
    expected = {
        1: {
            "source": "264e82bf9869ae3d28fe36dc5a2f82e24e53c1b59a35c7e04e2a44d8a2704855",
            "manifest": "48382e41b6aaf9cb6174891072b04efe8d65676ebb694cf9628cbe81c822b1dc",
            "log": "b2b214545dd05d88fc06c6e109a1e7380d23c8ea1aae0a1d4ba17d69a1d57fdd",
            "exit": 1,
            "rss": 6_832_320,
            "audits": 5,
        },
        2: {
            "source": "621ad297e6b7248cc40f6da0060db205e01f0977fb97c46882794f01f055f64a",
            "manifest": "4b93c734de4ffcbe03b01df2af47666bcccaccdd6be1b9d9768bdb26625c9ac4",
            "log": "4e16b0e265e687e3b1e31860429b4828f36e800a5f0a220c8a9dcf8a92e8da7b",
            "exit": 0,
            "rss": 6_877_452,
            "audits": 7,
        },
    }
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for version, want in expected.items():
        tag = f"early-c1-higher-y-support-nuc-v{version}"
        paths = {
            "source": EX / f"{tag}-source.txt",
            "manifest": EX / f"{tag}-manifest.json",
            "log": EX / f"{tag}.log",
        }
        assert all(sha(paths[key]) == want[key] for key in paths)
        log = paths["log"].read_text()
        assert f"LEAN_EXIT={want['exit']}" in log
        assert f"Maximum resident set size (kbytes): {want['rss']}" in log
        assert re.search(r"Swaps:\s*0\b", log)
        audits = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", log, re.S)
        assert len(audits) == want["audits"]
        if version == 2:
            assert all(
                {a.strip() for a in used.split(",") if a.strip()} <= allowed
                for _, used in audits
            )
            assert "sorryAx" not in log and "PROVENANCE_UNCHANGED=true" in log
    olean = EX / "EarlyC1HigherYSupport.olean"
    if olean.exists():
        assert sha(olean) == "b6d6de6883a3ca7ad71e4e0c00736335acddb04649b966e73966f35b4c9450d3"

    saved = json.loads((RD / "higher-y-fixed-c1-screen.json").read_text())
    dense = Fraction(
        int(saved["terms"]["dense_total"]["numerator"]),
        int(saved["terms"]["dense_total"]["denominator"]),
    )
    assert dense * 2**100 < 1
    assert saved["high_support_begins"] == 200_808
    assert saved["higher_parent_weight"] == 117_077
    assert saved["proof_body_bytes"] == 40_282
    assert saved["grinding_credit_bits"] == 0
    print("EARLY_C1_HIGHER_Y_AUDIT_PASS: v2 green; 7 standard-only audits; exact screen < 2^-100")


if __name__ == "__main__":
    main()
