#!/usr/bin/env python3
"""Stage EXPLICIT candidate iterator models; not a certified compiler pass."""
import argparse
import hashlib
import json
from pathlib import Path

FUNS_PIN = "e8b29608ef90d72b4dd3d8b0697f6619fb0e4896fdb475cdd8725fff4cc80fa3"
TYPES_PIN = "51e47fa8908d7776913478ae49e944d4de16777d9966fc33eadc50935c0e3554"


def pinned(path, expected):
    data = path.read_bytes()
    assert hashlib.sha256(data).hexdigest() == expected, f"pin mismatch: {path}"
    return data.decode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("raw", type=Path)
    parser.add_argument("destination", type=Path)
    parser.add_argument("--check", action="store_true", help="validate existing stage without writing")
    args = parser.parse_args()
    assert args.check or not args.destination.exists(), "fresh destination required"
    source = pinned(args.raw / "Funs.lean", FUNS_PIN)
    types = pinned(args.raw / "Types.lean", TYPES_PIN)
    changes = []

    def replace(old, new, count=1):
        nonlocal source
        assert source.count(old) == count, (old, source.count(old), count)
        source = source.replace(old, new)
        changes.append({"old": old, "new": new, "count": count})

    replace("import Aeneas\n", "import Aeneas.Std\nimport Aeneas.Data.Discriminant\nimport Aeneas.Tactic.RustAttributes\n")
    replace("import AspisR17MaskSource.FunsExternal", "import AspisR17MaskSource.IteratorCompat")
    replace("core.ops.function.FnMut", "IteratorCompat.BorrowFnMut", 2)
    replace("core.ops.function.FnOnce", "IteratorCompat.BorrowFnOnce")
    replace("next := core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next",
            "next := IteratorCompat.mapNext")
    replace("next := core.slice.iter.IteratorIterMut.next", "next := IteratorCompat.iterMutNextForward")
    replace("core.iter.traits.iterator.Iterator.map.default", "IteratorCompat.mapDefault")
    replace("core.iter.traits.iterator.Iterator.collect.default", "IteratorCompat.collectState")
    replace("      (core.iter.traits.collect.FromIteratorVec field.QM31) m", "      m")
    replace("core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next\n"
            "      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT\n"
            "      field.QM31) (core.iter.traits.iterator.IteratorVecIntoIter field.QM31)\n"
            "      iter", "IteratorCompat.zipMutNext iter")
    replace("core.iter.traits.iterator.Iterator.zip.trait_default\n"
            "        (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT\n"
            "        field.QM31) (core.iter.traits.collect.IntoIteratorVec field.QM31) im v",
            "IteratorCompat.zipMutVec im v")
    assert "axiom " not in source and "sorry" not in source
    assert types.count("import Aeneas\n") == 1
    types = types.replace("import Aeneas\n", "import Aeneas.Std.Scalar.Core\n")
    target = args.destination / "AspisR17MaskSource"
    files = {"Types.lean": types.encode(), "Funs.lean": source.encode()}
    extras = {}
    for name in ("IteratorCompat.lean", "IteratorLaws.lean", "AuditCaller.lean"):
        data = Path(__file__).with_name(name).read_bytes()
        files[name] = data
        extras[name] = hashlib.sha256(data).hexdigest()
    manifest = {
        "status": "candidate compatibility model, source refinement OPEN",
        "raw_funs_sha256": FUNS_PIN, "raw_types_sha256": TYPES_PIN,
        "changes": changes,
        "extra_sha256": extras,
        "staged_funs_sha256": hashlib.sha256(source.encode()).hexdigest(),
    }
    if args.check:
        for name, data in files.items():
            assert (target / name).read_bytes() == data, f"staged file mismatch: {name}"
        assert json.loads((args.destination / "iterator-stage.json").read_text()) == manifest
    else:
        target.mkdir(parents=True)
        for name, data in files.items():
            (target / name).write_bytes(data)
        (args.destination / "iterator-stage.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps({"changes": len(changes), "checked": args.check,
                      "destination": str(args.destination)}))


if __name__ == "__main__":
    main()
