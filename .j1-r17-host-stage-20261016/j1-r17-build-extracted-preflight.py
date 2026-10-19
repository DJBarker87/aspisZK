#!/usr/bin/env python3
"""Small source-only regression for the extracted-port runner; never runs Lean."""
import argparse
import json
from pathlib import Path
import runpy
import tempfile


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("staged_sources", type=Path)
    ap.add_argument("--current-object", type=Path)
    ap.add_argument("--old-object", type=Path)
    args = ap.parse_args()
    script = Path(__file__).with_name("j1-r17-build-extracted.py")
    compile(script.read_text(), str(script), "exec")
    api = runpy.run_path(str(script), run_name="runner_test")
    checks = []
    with tempfile.TemporaryDirectory(prefix="j1-r17-runner-preflight-") as temp:
        root = Path(temp); source = root / "Imports.lean"
        source.write_text("/- outer /- import Wrong -/ -/\nmodule\npublic meta import all Foo.Bar\nprivate import Baz Qux\n")
        assert api["imports"](source, True) == ["Init", "Foo.Bar", "Baz", "Qux"]
        source.write_text("prelude\nimport Init.Prelude\n")
        assert api["imports"](source, True) == ["Init.Prelude"]
        checks.append("nested comments, public/meta/all imports, implicit Init and prelude")
        source.write_text("#print axioms x\n#print axioms y\n")
        assert api["audits"](source, "'x' depends on axioms: [propext, Classical.choice, Quot.sound]\n'y' does not depend on any axioms\n")["passed"]
        assert not api["audits"](source, "'x' depends on axioms: [sorryAx]\n'y' does not depend on any axioms\n")["passed"]
        assert not api["audits"](source, "'x' depends on axioms: [propext]\n")["passed"]
        checks.append("axiom audit rejects missing reports and sorryAx")
        (root / "sources").symlink_to(args.staged_sources.resolve(), target_is_directory=True)
        manifest = api["staged"](root)
        assert len(manifest["modules"]) == 85
        assert api["selected"](manifest, ["PublicSerializerFieldsRefinement431"], []) == [
            "AspisR1PublicSerializer.Types", "AspisR1PublicSerializer.Funs", "PublicSerializerFieldsRefinement431"]
        assert len(api["selected"](manifest, [], ["final_public_bridge"])) == 41
        checks.append("85 source/import pins; first closure 3 targets; final bridge closure 41")
        data = {"runtime_files": {"lean": "compiler"}, "modules": {
            "A": {"source_sha256": "a", "objects": {".olean": {"sha256": "oa"}}, "imports": []},
            "B": {"source_sha256": "b", "objects": {".olean": {"sha256": "ob"}}, "imports": ["A"]},
            "C": {"source_sha256": "c", "objects": {".olean": {"sha256": "oc"}}, "imports": []}}}
        first = api["external_keys"](data); data["captured_utc"] = "later"
        assert api["external_keys"](data) == first
        data["modules"]["A"]["objects"][".olean"]["sha256"] = "changed"
        second = api["external_keys"](data)
        assert first["A"] != second["A"] and first["B"] != second["B"] and first["C"] == second["C"]
        checks.append("transitive object changes invalidate dependents only; timestamp does not")
        if args.current_object:
            assert api["object_header"](args.current_object)
            checks.append("current 4.32 object header accepted")
        if args.old_object:
            try:
                api["object_header"](args.old_object)
            except ValueError as error:
                assert "Non-4.32" in str(error)
            else:
                raise AssertionError("Old compiler object was accepted")
            checks.append("old compiler object rejected before use")
    print(json.dumps({"scope": "Python/source-only; no Lean, Lake, host or extraction command", "checks": checks}, indent=2))


if __name__ == "__main__":
    main()
