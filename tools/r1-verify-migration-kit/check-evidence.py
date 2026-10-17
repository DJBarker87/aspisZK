#!/usr/bin/env python3
"""Read/hash-only replay of complete native verify/query evidence; no builds."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import resource
import subprocess
import sys
import tarfile
import tempfile
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SEM = "crates/aspis-r1-cost-probe/src/r1_semantic.rs"
TRANSCRIPT = "crates/aspis-r1-cost-probe/src/transcript.rs"
FINAL = "a555c852664c80000942f0c911e16719a5493625"
QUERY = "5a28a4b4896aba8b07bff11c47d4683dea3c80cf"
BEFORE = "deb68369ba3ad7cc6706dc24b6503fac1cbe942b"
sha = lambda raw: hashlib.sha256(raw).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("archive", type=Path)
    ap.add_argument("--sha256", required=True)
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    start = time.monotonic()
    raw_archive = args.archive.read_bytes()
    assert sha(raw_archive) == args.sha256
    with tarfile.open(args.archive) as tf:
        files = {m.name: tf.extractfile(m).read() for m in tf.getmembers() if m.isfile()}
    read_json = lambda p: json.loads(files[p])
    clean = read_json("verify-final/clean-production-inputs.json")
    assert clean["source_revision"] == FINAL and len(clean["files"]) == 532
    source_paths = [name.removeprefix("source/") for name in clean["files"]]
    requests = [(FINAL, path) for path in source_paths] + [(QUERY, SEM), (BEFORE, SEM), (QUERY, TRANSCRIPT)]
    proc = subprocess.run(["git", "-C", str(ROOT), "cat-file", "--batch"],
        input="".join(rev + ":" + path + "\n" for rev, path in requests).encode(), capture_output=True, check=True)
    blobs = {}; offset = 0
    for key in requests:
        end = proc.stdout.index(b"\n", offset)
        header = proc.stdout[offset:end].split(); assert header[1] == b"blob", header
        size = int(header[2]); offset = end + 1
        blobs[key] = proc.stdout[offset:offset + size]
        offset += size + 1
    assert offset == len(proc.stdout)
    assert blobs[QUERY, TRANSCRIPT] == blobs[FINAL, TRANSCRIPT]
    changed = subprocess.check_output(["git", "-C", str(ROOT), "diff", "--name-only", QUERY, FINAL,
        "--", "crates", "programs"], text=True).splitlines()
    assert changed == [SEM]
    spec = importlib.util.spec_from_file_location("verify_overlay", HERE / "prepare.py")
    overlay = importlib.util.module_from_spec(spec); spec.loader.exec_module(overlay)
    old = overlay.declaration(blobs[BEFORE, SEM], "pub fn verify_observed<")
    old, _ = overlay.instrument(old)
    old = old.replace(b"pub fn verify_observed<", b"fn migration_old_verify_observed<", 1)
    snapshots = {"verify-final": FINAL, "verify-historical": QUERY, "query": QUERY}
    for prefix, revision in snapshots.items():
        manifest = read_json(prefix + "/inputs.json")
        assert manifest["source_revision"] == revision
        for name, digest in manifest["files"].items():
            assert sha(files[prefix + "/" + name]) == digest, (prefix, name)
        for name in source_paths:
            raw = blobs[revision, SEM] if name == SEM else blobs[FINAL, name]
            if name == SEM:
                raw, _ = overlay.instrument(raw)
                raw += ("\n" + overlay.CFG + "\n").encode() + old + ("\n" + overlay.CFG +
                    '\n#[path="verify_migration_tests.rs"]\nmod verify_migration_tests;\n').encode()
            elif name == TRANSCRIPT and prefix == "query":
                continue  # Complete query overlay separately pinned below.
            assert files[prefix + "/source/" + name] == raw, (prefix, name)
        vpins = read_json(prefix + "/source/verify-migration-overlay.json")
        for name, digest in vpins["overlay_files"].items():
            assert sha(files[prefix + "/source/" + name]) == digest
    qpins = read_json("query/source/query-migration-overlay.json")
    assert qpins["after"] == QUERY
    assert qpins["production_source_sha256"] == sha(blobs[QUERY, TRANSCRIPT])
    for name, digest in qpins["overlay_files"].items():
        assert sha(files["query/source/" + name]) == digest
    context = read_json("query/source/crates/aspis-r1-cost-probe/src/query_migration_context.json")
    counter = read_json("query/query-context-origin-counter.json")
    calls = counter["ordered_digest_calls"]; at = context["ordered_call_index"]
    assert len(calls) == 583 and context["expected17calls"] == calls[at:at + 17]
    assert counter["source_revision"] == context["source_counter_revision"]
    assert calls[at]["parts_hex"][0] == context["state_hex"]
    assert calls[at]["parts_hex"][-1] == context["payload_hex"]
    assert calls[at]["output_hex"] == context["expected_absorbed_state"]
    targets = [("verify-final", "verify-real-s2-default", "false"),
               ("verify-final", "verify-real-s2-detail", "true"),
               ("query", "query-migration-102", None)]
    summaries = []
    for prefix, label, detail in targets:
        run = prefix + "/runs/" + label + "/"
        receipt = read_json(run + "receipt.json")
        assert receipt["exit_status"] == receipt["process_swaps"] == 0
        assert receipt["source_revision"] == snapshots[prefix]
        assert receipt["cgroup_swap_current"] == "0"
        assert receipt["limits"] == {"memory.high": "6442450944", "memory.max": "8589934592", "memory.swap.max": "0"}
        assert "--release" in receipt["command"] and "-j1" in receipt["command"]
        assert receipt["input_manifest_sha256"] == sha(files[prefix + "/inputs.json"])
        assert receipt["runner_sha256"] == sha(files[run + "runner.py"])
        for stream in ["stdout", "stderr"]:
            assert receipt[stream + "_sha256"] == sha(files[run + stream + ".log"])
        assert files[run + "input-manifest.json"] == files[prefix + "/inputs.json"]
        reservation = read_json(prefix + "/" + label + "-reservation.json")
        assert reservation["source_revision"] == snapshots[prefix]
        assert reservation["total_with_new_bytes"] < reservation["safe_working_limit_bytes"] == 55 * 2**30
        with tempfile.TemporaryDirectory(prefix="verify-query-log-check-") as td:
            log = Path(td) / "stdout.log"; log.write_bytes(files[run + "stdout.log"])
            checker = HERE / "check-log.py" if detail is not None else ROOT / "tools/r1-query-migration-kit/check-log.py"
            command = [sys.executable, str(checker), str(log)]
            if detail is not None: command += ["--detail", detail]
            checked = subprocess.run(command, capture_output=True, text=True, check=True)
        summaries.append({k: receipt[k] for k in ["label", "source_revision", "exit_status", "wall_seconds", "peak_rss_kib", "process_swaps", "axioms"]} |
            {"coverage_check": checked.stdout.strip()})
    own, children = resource.getrusage(resource.RUSAGE_SELF), resource.getrusage(resource.RUSAGE_CHILDREN)
    result = {"status": "PASS", "target": str(Path(__file__).relative_to(ROOT)),
        "command_argv": [sys.executable, *sys.argv], "exit_status": 0,
        "wall_seconds": time.monotonic() - start,
        "peak_rss_bytes": max(own.ru_maxrss, children.ru_maxrss) * (1 if sys.platform == "darwin" else 1024),
        "swap_events": own.ru_nswap + children.ru_nswap,
        "source_revision": FINAL, "checker_revision": subprocess.check_output(["git", "-C", str(ROOT), "rev-parse", "HEAD"], text=True).strip(),
        "print_axioms": "N/A (read/hash-only evidence check)", "members": len(files), "production_files_each_snapshot": 532,
        "accepted_targets": summaries, "final_verify_cases": 224, "query_cases": 102,
        "query_repin": "Entire transcript.rs and all530 other production files unchanged; only semantic round source differs",
        "historical_verify_targets": "5a28 snapshots retained; superseded by final a555 checks",
        "archive_sha256": args.sha256, "builds_executed": False, "SBF_build": False, "readonly_runtime_harness": False}
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ["status", "members", "final_verify_cases", "query_cases", "builds_executed"]}))


if __name__ == "__main__":
    main()
