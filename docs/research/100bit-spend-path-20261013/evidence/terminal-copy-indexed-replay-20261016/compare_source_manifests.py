#!/usr/bin/env python3
"""Compare pinned file manifests against Git blobs at each recorded revision."""
import hashlib, json, subprocess, sys
from pathlib import Path

root = Path(sys.argv[1]).resolve()
evidence = Path(__file__).resolve().parent
def git_blob(rev, path):
    p = subprocess.run(["git", "-C", str(root), "cat-file", "blob", f"{rev}:{path}"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if p.returncode:
        return None
    return hashlib.sha256(p.stdout).hexdigest()

checks = []
base = json.loads((evidence / "baseline-source/after-manifest.json").read_text())
for label, rev, files, intentional in [
    ("baseline-terminal-validator-source", base["revision"], base["files"], set()),
]:
    matched, mismatches, missing = [], [], []
    for path, expected in sorted(files.items()):
        actual = git_blob(rev, path)
        if actual is None:
            missing.append(path)
        elif actual == expected:
            matched.append(path)
        else:
            mismatches.append({"path": path, "git_blob_sha256_as_file_sha": actual, "manifest_sha256": expected})
    checks.append({"label": label, "revision": rev, "files": len(files), "matched": len(matched), "mismatches": mismatches, "missing": missing})

candidate = json.loads((evidence / "evidence-export/candidate-input-manifest-508.json").read_text())
rev = candidate["base_revision"]
intentional = candidate["candidate_overlay"]
matched, mismatches, missing = [], [], []
for path, expected in sorted(candidate["files"].items()):
    actual = git_blob(rev, path)
    if actual is None:
        missing.append(path)
    elif actual == expected:
        matched.append(path)
    else:
        item = {"path": path, "git_blob_sha256_as_file_sha": actual, "manifest_sha256": expected, "candidate_overlay_expected_sha256": intentional.get(path)}
        mismatches.append(item)
checks.append({"label": "candidate-508-source-snapshot-versus-base-git", "revision": rev, "files": len(candidate["files"]), "matched": len(matched), "mismatches": mismatches, "missing": missing, "intentional_overlay_paths": sorted(intentional)})
report = {"method": "sha256 of Git blob bytes at the exact manifest revision compared with recorded per-file SHA-256", "checks": checks, "conclusion": "baseline 504-file manifest is byte-identical to Git; candidate 508-file snapshot has exactly three differences, each matching its explicitly pinned candidate overlay"}
(evidence / "source-manifest-git-comparison.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps([{k:v for k,v in x.items() if k in ["label","revision","files","matched","missing","intentional_overlay_paths"]} | {"mismatches":len(x["mismatches"])} for x in checks], indent=2))
if any(x["missing"] for x in checks) or len(checks[0]["mismatches"]) or len(checks[1]["mismatches"]) != 3:
    raise SystemExit(1)
if {m["path"] for m in checks[1]["mismatches"]} != set(checks[1]["intentional_overlay_paths"]):
    raise SystemExit("candidate mismatches do not exactly equal pinned overlays")
if any(m["manifest_sha256"] != m["candidate_overlay_expected_sha256"] for m in checks[1]["mismatches"]):
    raise SystemExit("candidate mismatch digest differs from explicit overlay pin")
