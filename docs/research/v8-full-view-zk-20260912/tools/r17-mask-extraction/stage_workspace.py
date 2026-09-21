#!/usr/bin/env python3
"""Stage the new buffer source extraction with import-only compatibility edits."""
import argparse
import hashlib
from pathlib import Path


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("raw", type=Path)
    p.add_argument("destination", type=Path)
    p.add_argument("--check", action="store_true")
    args = p.parse_args()
    assert args.check or not args.destination.exists(), "fresh output required"
    pins = {
        "Types.lean": "a29d7a2e4067ece0ff887ebb0eff3a3e49f28aa6436cdba289bf9b3c07c5cc33",
        "Funs.lean": "951d864bcc7238e6e61eaed240632fe7eb90e7d132ab63b97d75b9acef095b8f",
    }
    staged = {}
    for name, pin in pins.items():
        data = (args.raw / name).read_bytes()
        assert hashlib.sha256(data).hexdigest() == pin, name
        text = data.decode()
        assert text.count("import Aeneas\n") == 1
        assert "axiom " not in text and "sorry" not in text and "External" not in text
        replacement = "import Aeneas.Std.Scalar.Core\n" if name == "Types.lean" else (
            "import Aeneas.Std\nimport Aeneas.Data.Discriminant\nimport Aeneas.Tactic.RustAttributes\n")
        staged[name] = text.replace("import Aeneas\n", replacement)
    target = args.destination / "AspisR17MaskSource"
    if not args.check:
        target.mkdir(parents=True)
    for name, text in staged.items():
        if args.check:
            assert (target / name).read_text() == text, name
        else:
            (target / name).write_text(text)
    audit = Path(__file__).with_name("AuditWorkspace.lean").read_bytes()
    if args.check:
        assert (target / "AuditWorkspace.lean").read_bytes() == audit
    else:
        (target / "AuditWorkspace.lean").write_bytes(audit)
    print("PASS: raw pins; import-only staging, no declaration/body replacement")


if __name__ == "__main__":
    main()
