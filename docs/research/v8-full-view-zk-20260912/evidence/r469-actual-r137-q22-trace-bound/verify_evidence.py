#!/usr/bin/env python3
from pathlib import Path
import hashlib, json

E = Path(__file__).resolve().parent
DOCS = E.parent.parent

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def check(value, message):
    if not value:
        raise SystemExit("FAIL: " + message)

manifest = json.loads((E / "manifest.json").read_text())
for line in (E / "SHA256SUMS").read_text().splitlines():
    digest, relative = line.split("  ", 1)
    path = E / relative
    check(path.is_file() and sha(path) == digest, "checksum " + relative)

for label in ("successful", "rejected-attempt-1"):
    directory = E / label
    receipt = json.loads((directory / "receipt.json").read_text())
    log = (directory / "log.txt").read_text()
    check(receipt["target"] == manifest["successful_target"], label + " target")
    check(sha(directory / "source.lean") == receipt["source_sha256"], label + " source hash")
    check(f'Exit status: {receipt["exit_status"]}' in log, label + " exit")
    check(f'Elapsed (wall clock) time (h:mm:ss or m:ss): {receipt["wall_time"]}' in log, label + " wall")
    check(f'Maximum resident set size (kbytes): {receipt["peak_rss_kib"]}' in log, label + " RSS")
    check("Swaps: 0" in log and receipt["swaps"] == 0, label + " swap")
    check((directory / "command.txt").read_text().strip() in log, label + " command")
    resources = receipt["resources"]
    check(resources == manifest["resources"], label + " limits")
    for axiom in receipt["complete_print_axioms"]:
        check(axiom in log, label + " complete axiom report")

success = json.loads((E / "successful" / "receipt.json").read_text())
canonical = DOCS / "lean" / success["target"]
check(canonical.is_file() and sha(canonical) == success["source_sha256"], "promoted source identity")
check(success["exit_status"] == 0 and success["source_revision"] == manifest["source_revision"], "successful receipt")
check(success["complete_print_axioms"] == manifest["successful_complete_print_axioms"], "complete axiom list")
check(sha(E / "runner" / "run_focus.py") == manifest["runner_sha256"], "runner hash")
for module, item in json.loads((E / "linked-imports.json").read_text())["direct_imports"].items():
    path = (E / item["path"]).resolve()
    check(path.is_file() and sha(path) == item["sha256"] == manifest["direct_import_sha256"][module], "import " + module)

failed = json.loads((E / "rejected-attempt-1" / "receipt.json").read_text())
check(failed["exit_status"] == 1 and any("sorryAx" in item for item in failed["complete_print_axioms"]), "rejected history classification")
print("PASS: R469 source, receipts, logs, commands, axiom report, direct imports, runner, and checksums")
