#!/usr/bin/env python3
"""Read-only receipt audit for the authorized one-module decoder cache append."""
import hashlib
import json
from pathlib import Path
import subprocess
import append_ordinary_decoder_cache as append

EX = Path(__file__).resolve().parent
RD = EX.parent
base = append.base


def main():
    receipt = json.loads((RD / "ordinary-decoder-cache-append.json").read_text())
    plan = json.loads((EX / "ordinary-decoder-cache-plan.json").read_text())
    before = EX / "ordinary-decoder-cache-before-manifest.json"
    after = EX / "ordinary-decoder-cache-after-manifest.json"
    state = EX / "ordinary-decoder-cache-before-green-outputs.json"
    run = EX / plan["run_manifest_name"]
    for path, expected in (
        (before, append.BASE_SHA), (after, receipt["after_manifest_sha256"]),
        (state, plan["green_state_sha256"]), (run, plan["run_manifest_sha256"]),
        (EX / "append_ordinary_decoder_cache.py", receipt["helper_sha256"]),
        (EX / "append_ordinary_raw_cache.py", receipt["shared_helper_sha256"]),
        (EX / "ordinary-decoder-cache-bridge.trace", append.TRACE),
    ):
        base.require(base.sha(path) == expected, "retained decoder append changed: " + path.name)
    base.require(receipt["plan"] == plan and receipt["source_parent"] == base.SOURCE_PARENT and
                 receipt["borrowed"] == base.BORROWED and receipt["overlay_parent"] == base.RUN_PARENT,
                 "decoder append provenance pins changed")
    b, a, r = (json.loads(path.read_text()) for path in (before, after, run))
    base.require(len(b["files"]) == 798 and len(a["files"]) == 800 and len(r["files"]) == 865 and
                 len(json.loads(state.read_text())) == 34, "decoder append census changed")
    base.require(a["files"][:798] == b["files"] and a["files"][798:] == receipt["added"],
                 "decoder append replaced existing entries")
    base.require({k: v for k, v in a.items() if k not in ("files", "counts")} ==
                 {k: v for k, v in b.items() if k not in ("files", "counts")},
                 "decoder append changed unrelated metadata")
    base.require(a["counts"] == {"pinned_source_blobs": 400, "compiled_artifacts": 400},
                 "decoder append counts changed")
    base.require({(e["module"], e["kind"]): e["sha256"] for e in receipt["added"]} == {
        (append.MODULE, "source"): append.SOURCE, (append.MODULE, "olean"): append.OUTPUT},
        "unexpected decoder module or output variant")
    for entry in receipt["added"]:
        base.require(base.sha(Path(entry["local"])) == entry["sha256"], "local decoder import changed")
        if entry["kind"] == "source":
            blob = subprocess.check_output(["git", "-C", str(EX), "show",
                base.BORROWED + ":AspisFormal/" + entry["overlay"]])
            base.require(hashlib.sha256(blob).hexdigest() == entry["sha256"], "borrowed decoder source mismatch")
    indexed = {(e["module"], e["kind"]): e for e in r["files"]}
    for module, source, output in append.BOUNDARY:
        for kind, expected in (("source", source), ("olean", output)):
            entry = indexed[(module, kind)]
            base.require(entry["sha256"] == expected and base.sha(Path(entry["local"])) == expected,
                         "decoder boundary changed: " + module)
    log = (EX / "ordinary-decoder-cache-append.log").read_text()
    base.require(json.loads(log[:log.rfind("\nORDINARY_DECODER_CACHE_APPEND_PASS=2")]) == receipt,
                 "decoder receipt differs from terminal log")
    base.require(receipt["compiler_launched"] is False and receipt["native_variant_replacements"] == 0 and
                 receipt["retained_trace"]["new_axiom_credit"] == 0,
                 "decoder append scope overclaim")
    print("ORDINARY_DECODER_CACHE_AUDIT_PASS: 1 local pair, 3 unchanged boundary pairs; no new theorem credit.")


if __name__ == "__main__":
    main()
