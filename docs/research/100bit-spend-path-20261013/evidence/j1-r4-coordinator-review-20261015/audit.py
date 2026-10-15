"""Check retained J1.R2 evidence and the retrospective J1.R4 source-pin repair.

This validates bytes and recorded receipts; it does not execute Lean.
"""
import hashlib
import json
from pathlib import Path
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[5]
STUDY = ROOT / "docs/research/100bit-spend-path-20261013"
EVIDENCE = STUDY / "evidence"
BASE = "136b746805f3438507732622c9b4e50f36bf49f9"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def bundle_reader(bundle):
    archived = {}
    for archive in sorted(bundle.rglob("*.tar.gz")):
        with tarfile.open(archive) as stream:
            for member in stream.getmembers():
                if member.isfile():
                    archived[member.name] = stream.extractfile(member).read()

    def read(name):
        path = bundle / name
        return path.read_bytes() if path.is_file() else archived[name]

    return read


report = {
    "base": BASE,
    "scope": "Source and retained evidence audit, not a new compilation.",
    "append": [],
}
for name in ["lean-spend-append-binding-20261015", "lean-semantic-payload-view-20261015"]:
    bundle = EVIDENCE / name
    read = bundle_reader(bundle)
    lines = (bundle / "SHA256SUMS").read_text().splitlines()
    for line in lines:
        expected, path = line.split("  ", 1)
        assert digest(read(path)) == expected, (name, path)
    manifest = json.loads((bundle / "source-manifest.json").read_text())
    if name == "lean-spend-append-binding-20261015":
        for target in manifest["targets"]:
            current = (ROOT / target["local_source_path"]).read_bytes()
            assert current == read("sources/" + target["module"] + ".lean")
            assert digest(current) == target["source_sha256"]
            assert digest(read(target["object_path"])) == target["object_sha256"]
            attempt = next(a for a in manifest["attempts"] if a["target"] == target["module"])
            receipt = json.loads(read(attempt["receipt"]))
            assert receipt["exit_status"] == 0
            assert receipt["source_sha256"] == digest(current)
            output = read(attempt["out_log"]).decode()
            assert "sorryAx" not in output
            for axiom_line in target["axiom_output"]:
                assert axiom_line in output
            report["append"].append({
                "module": target["module"],
                "source_sha256": digest(current),
                "source_matches_snapshot": True,
                "receipt": str((bundle / attempt["receipt"]).relative_to(ROOT)),
                "wall": receipt["elapsed_wall_clock"],
                "max_rss_kib": receipt["max_rss_kib"],
                "swaps": receipt["swaps"],
                "axioms": target["axiom_output"],
            })
        report["append_bundle_checksum_members"] = len(lines)
    else:
        for entry in manifest["files"]:
            data = read(entry["path"])
            assert len(data) == entry["size_bytes"]
            assert digest(data) == entry["sha256"]
        sources = []
        for entry in manifest["direct_imports"]:
            relative = (
                "docs/research/100bit-spend-path-20261013/lean/SemanticRecordCodec.lean"
                if entry["module"] == "R1SemanticRecordCodec" else
                "docs/research/v8-r0-sem-proof-20261008/lean/R0P/MaskView.lean"
            )
            data = read(entry["source"])
            assert (ROOT / relative).read_bytes() == data
            historic = subprocess.check_output(
                ["git", "show", manifest["source_revision"] + ":" + relative], cwd=ROOT)
            assert historic == data
            assert digest(data) == entry["source_sha256"]
            sources.append({"module": entry["module"], "sha256": digest(data),
                            "matches_current_and_original_source_revision": True})
        original = subprocess.check_output(
            ["git", "show", manifest["source_pin_repair"]["original_manifest_git_object"]], cwd=ROOT)
        assert digest(original) == manifest["source_pin_repair"]["original_manifest_sha256"]
        report["payload_pin_repair"] = {
            "checksum_members": len(lines), "manifest_members": len(manifest["files"]),
            "manifest_sha256": digest((bundle / "source-manifest.json").read_bytes()),
            "sources": sources, "compile_time_import_source_attestation": False,
            "replay_performed": False,
        }

output = Path(__file__).with_name("source-evidence-audit.json")
output.write_text(json.dumps(report, indent=2) + "\n")
print("Verified", report["append_bundle_checksum_members"], "append checksum entries and",
      report["payload_pin_repair"]["checksum_members"], "repaired payload checksum entries.")
