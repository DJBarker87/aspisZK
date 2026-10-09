#!/usr/bin/env python3
"""Read-only local verification of the authorized two-module cache append."""
import hashlib
import json
from pathlib import Path
import subprocess
import append_ordinary_raw_cache as append

EX = Path(__file__).resolve().parent
RD = EX.parent


def main():
    receipt = json.loads((RD / "ordinary-raw-cache-append.json").read_text())
    before = EX / "ordinary-raw-cache-before-manifest.json"
    after = EX / "ordinary-raw-cache-after-manifest.json"
    state = EX / "ordinary-raw-cache-before-green-outputs.json"
    run = EX / append.RUN_NAME
    for path, expected in ((before, append.BASE_SHA), (state, append.STATE_SHA), (run, append.RUN_SHA),
                           (after, receipt["after_manifest_sha256"]),
                           (EX / "append_ordinary_raw_cache.py", receipt["helper_sha256"])):
        append.require(append.sha(path) == expected, "retained append metadata changed: " + path.name)
    append.require(receipt["source_parent"] == append.SOURCE_PARENT and
                   receipt["borrowed"] == append.BORROWED and receipt["overlay_parent"] == append.RUN_PARENT,
                   "append source/runner pins changed")
    b, a, r = (json.loads(path.read_text()) for path in (before, after, run))
    append.require(len(b["files"]) == 794 and len(a["files"]) == 798 and len(r["files"]) == 859,
                   "append entry census changed")
    append.require(a["files"][:794] == b["files"] and a["files"][794:] == receipt["added"],
                   "append replaced an existing entry")
    append.require({k: v for k, v in a.items() if k not in ("files", "counts")} ==
                   {k: v for k, v in b.items() if k not in ("files", "counts")},
                   "append changed unrelated metadata")
    append.require(a["counts"] == {"pinned_source_blobs": 399, "compiled_artifacts": 399},
                   "append counts changed")
    expected = {(module, kind): value for module, source, output, _, _ in append.PAIRS
                for kind, value in (("source", source), ("olean", output))}
    append.require({(e["module"], e["kind"]): e["sha256"] for e in receipt["added"]} == expected,
                   "unexpected imported module or variant")
    for entry in receipt["added"]:
        append.require(append.sha(Path(entry["local"])) == entry["sha256"], "local import bytes changed")
        if entry["kind"] == "source":
            blob = subprocess.check_output(["git", "-C", str(EX), "show",
                append.BORROWED + ":AspisFormal/" + entry["overlay"]])
            append.require(hashlib.sha256(blob).hexdigest() == entry["sha256"], "borrowed source mismatch")
    indexed = {(entry["module"], entry["kind"]): entry for entry in r["files"]}
    for module, source, output in append.BOUNDARY:
        for kind, expected_sha in (("source", source), ("olean", output)):
            entry = indexed[(module, kind)]
            append.require(entry["sha256"] == expected_sha and
                           append.sha(Path(entry["local"])) == expected_sha,
                           "existing boundary changed: " + module)
    for path, pair in zip((EX / "ordinary-raw-cache-stopping.trace",
                           EX / "ordinary-raw-cache-eight-retry.trace"), append.PAIRS):
        append.require(append.sha(path) == pair[3], "retained local trace changed")
    log = (EX / "ordinary-raw-cache-append.log").read_text()
    append.require(json.loads(log[:log.rfind("\nORDINARY_RAW_CACHE_APPEND_PASS=4")]) == receipt,
                   "append receipt differs from terminal log")
    append.require(receipt["compiler_launched"] is False and receipt["native_variant_replacements"] == 0,
                   "append scope overclaim")
    print("ORDINARY_RAW_CACHE_AUDIT_PASS: 2 local pairs, 4 unchanged boundary pairs; no new theorem credit.")


if __name__ == "__main__":
    main()
