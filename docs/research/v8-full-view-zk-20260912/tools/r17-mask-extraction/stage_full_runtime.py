#!/usr/bin/env python3
"""Replay retained arithmetic proofs against actual runtime declarations.

The projection's authenticated runtime declaration copies are omitted because
the full cached runtime supplies them. All retained theorem statements/bodies
and generated field declarations remain unchanged. This is not an axiom bridge.
"""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

TARGETS = {"UnsignedCoreSlice": (12, []), "UnsignedCM31Cross": (5, ["--cross"]),
           "UnsignedReducerOps": (5, ["--reducer"])}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("proofs", type=Path)
    parser.add_argument("runtime_scalar", type=Path)
    parser.add_argument("checker", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    assert args.check or not args.output.exists(), "fresh destination required"
    staged = {}
    manifest = {}
    for name, (count, flags) in TARGETS.items():
        path = args.proofs / (name + ".lean")
        subprocess.run(["python3", str(args.checker), "--runtime", str(args.runtime_scalar),
                        "--slice", str(path), *flags], check=True)
        original = path.read_text()
        text, actual = re.subn(r"^-- SOURCE [^\n]+\n.*?^-- END SOURCE\n", "", original,
                               flags=re.MULTILINE | re.DOTALL)
        assert actual == count, (name, actual, count)
        if name == "UnsignedCoreSlice":
            imports = "import Aeneas.Std.Primitives\nimport AeneasMeta.BvEnumToBitVec\nimport Mathlib.Data.Nat.Notation\n"
            assert text.startswith(imports)
            text = "import Aeneas.Std\n" + text[len(imports):]
        # In particular the arithmetic theorem blocks are byte-identical.
        marker = "namespace AspisV8R17." + name + "\n"
        assert original.split(marker, 1)[1] == text.split(marker, 1)[1]
        staged[name] = text
        manifest[name] = {"original_sha256": hashlib.sha256(original.encode()).hexdigest(),
                          "staged_sha256": hashlib.sha256(text.encode()).hexdigest(),
                          "runtime_blocks_replaced_by_import": count}
    target = args.output / "AspisV8R17"
    extra = Path(__file__).with_name("FullRuntimeWrapping.lean").read_text()
    staged["FullRuntimeWrapping"] = extra
    manifest["FullRuntimeWrapping"] = {"staged_sha256": hashlib.sha256(extra.encode()).hexdigest()}
    if not args.check:
        target.mkdir(parents=True)
    for name, text in staged.items():
        if args.check:
            assert (target / (name + ".lean")).read_text() == text, name
        else:
            (target / (name + ".lean")).write_text(text)
    if args.check:
        assert json.loads((args.output / "full-runtime-stage.json").read_text()) == manifest
    else:
        (args.output / "full-runtime-stage.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print("PASS: runtime source checks; 3 retained theorem blocks unchanged; wrapping bridge included")


if __name__ == "__main__":
    main()
