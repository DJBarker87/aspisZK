#!/usr/bin/env python3
"""Validate the provisional focused Lean reuse checkpoint evidence."""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
import tarfile
from pathlib import Path


HERE = Path(__file__).resolve().parent
MANIFEST = HERE / "manifest.json"
EXPECTED_CGROUP = {
    "MemoryHigh": "4G",
    "MemoryMax": "6G",
    "MemorySwapMax": "0",
    "TasksMax": 128,
}
EXPECTED_LEAN_MB = 5000
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AXIOM_RE = re.compile(
    r"^'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)$",
    re.M | re.S,
)
IMPORT_RE = re.compile(r"^import\s+([^\s]+)\s*$", re.M)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fail(message: str) -> None:
    raise SystemExit(f"FAIL: {message}")


def main() -> None:
    manifest = json.loads(MANIFEST.read_text())
    root = Path(
        subprocess.check_output(
            ["git", "rev-parse", "--show-toplevel"], cwd=HERE, text=True
        ).strip()
    )
    head = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=root, text=True
    ).strip()
    capture_head = manifest["capture_worktree_head"]
    if head != capture_head:
        is_ancestor = subprocess.run(
            ["git", "merge-base", "--is-ancestor", capture_head, head], cwd=root
        ).returncode == 0
        if not is_ancestor:
            fail(f"capture HEAD {capture_head} is not an ancestor of worktree HEAD {head}")

    object_archive = None
    archive_record = manifest.get("compiled_objects_archive")
    if archive_record:
        archive_file = root / archive_record["path"]
        if not archive_file.is_file():
            fail(f"missing compiled object archive: {archive_file}")
        if sha256(archive_file) != archive_record["sha256"]:
            fail("compiled object archive hash mismatch")
        try:
            object_archive = tarfile.open(archive_file, "r:gz")
        except (OSError, tarfile.TarError) as error:
            fail(f"invalid compiled object archive: {error}")

    def check_object(path: Path, expected_hash: str, archive_member: str) -> None:
        if object_archive is not None:
            try:
                stream = object_archive.extractfile(archive_member)
            except KeyError:
                stream = None
            if stream is None:
                fail(f"missing compiled object archive member: {archive_member}")
            if hashlib.sha256(stream.read()).hexdigest() != expected_hash:
                fail(f"archived compiled object hash mismatch: {archive_member}")
        elif not path.is_file():
            fail(f"missing compiled object and no archive: {path}")
        if path.is_file() and sha256(path) != expected_hash:
            fail(f"compiled object hash mismatch: {path}")

    dependency_by_module = {
        item["module"]: item for item in manifest["dependency_sources"]
    }
    for dep in manifest["dependency_sources"]:
        src = root / dep["source_path"]
        obj = root / dep["compiled_object_path"]
        if not src.is_file():
            fail(f"missing dependency source for {dep['module']}")
        if sha256(src) != dep["source_sha256"]:
            fail(f"dependency source hash mismatch: {dep['module']}")
        check_object(
            obj,
            dep["compiled_object_sha256"],
            dep.get("compiled_object_archive_member", str(obj.relative_to(HERE))),
        )
        imports = IMPORT_RE.findall(src.read_text())
        if imports != dep["imports"]:
            fail(f"dependency import list changed: {dep['module']}")
        local_deps = [name for name in imports if name in dependency_by_module]
        if local_deps != dep["local_source_dependencies"]:
            fail(f"local dependency edge list changed: {dep['module']}")

    for target in manifest["targets"]:
        source_base = target.get("source_base_revision")
        if source_base is not None:
            is_ancestor = subprocess.run(
                ["git", "merge-base", "--is-ancestor", source_base, capture_head],
                cwd=root,
            ).returncode == 0
            if not is_ancestor:
                fail(f"source base is not an ancestor of capture HEAD: {target['module']}")
        elif not target.get("source_base_revision_note"):
            fail(f"missing source-base provenance note: {target['module']}")
        source = root / target["source_path"]
        if not source.is_file():
            fail(f"missing target source {target['source_path']}")
        source_hash = sha256(source)
        if source_hash != target["source_sha256"]:
            fail(f"target source hash mismatch: {target['module']}")

        files = target["files"]
        for key, expected_hash in target["artifact_sha256"].items():
            if key == "compiled_object" and object_archive is not None:
                object_path = root / files[key]
                check_object(
                    object_path,
                    expected_hash,
                    target.get(
                        "compiled_object_archive_member",
                        str(object_path.relative_to(HERE)),
                    ),
                )
                continue
            artifact = root / files[key]
            if not artifact.is_file():
                fail(f"missing {key} for {target['module']}: {artifact}")
            if sha256(artifact) != expected_hash:
                fail(f"{key} artifact hash mismatch: {target['module']}")

        receipt = json.loads((root / files["receipt"]).read_text())
        if receipt["target"] != target["module"] or receipt["attempt"] != target["attempt"]:
            fail(f"receipt target/attempt mismatch: {target['module']}")
        if receipt["exit_status"] != 0:
            fail(f"nonzero receipt status: {target['module']}")
        if receipt["source_sha256"] != source_hash:
            fail(f"receipt source hash mismatch: {target['module']}")
        sidecar_hash = (root / files["sidecar"]).read_text().split()[0]
        if sidecar_hash != source_hash:
            fail(f"source sidecar hash mismatch: {target['module']}")
        sidecar_parts = (root / files["sidecar"]).read_text().split()
        expected_remote_source = (
            f"{manifest['nuc_workspace']}/sources/{target['module']}.lean"
        )
        if len(sidecar_parts) < 2 or sidecar_parts[1] != expected_remote_source:
            fail(f"remote source path mismatch: {target['module']}")
        if receipt["cgroup"] != EXPECTED_CGROUP:
            fail(f"resource cap mismatch: {target['module']}")
        if receipt["lean_threshold_mb"] != EXPECTED_LEAN_MB:
            fail(f"Lean threshold mismatch: {target['module']}")
        wall_parts = receipt["elapsed_wall_clock"].split(":")
        try:
            seconds = sum(float(part) * (60 ** (len(wall_parts) - index - 1))
                          for index, part in enumerate(wall_parts))
        except ValueError:
            seconds = 0
        if seconds <= 0:
            fail(f"missing wall time: {target['module']}")
        rss = int(receipt["max_rss_kib"])
        if rss <= 0 or rss >= 6 * 1024 * 1024 or receipt["swaps"] != "0":
            fail(f"invalid RSS/swap receipt: {target['module']}")

        source_imports = IMPORT_RE.findall(source.read_text())
        if source_imports != target["imports"]:
            fail(f"target import list changed: {target['module']}")
        local_deps = [name for name in source_imports if name in dependency_by_module]
        if local_deps != target["local_source_dependencies"]:
            fail(f"target dependency edges changed: {target['module']}")
        for dep_name in local_deps:
            if dependency_by_module[dep_name]["source_sha256"] != target["dependency_source_sha256"][dep_name]:
                fail(f"dependency hash reference mismatch: {target['module']} -> {dep_name}")

        log = (root / files["output_log"]).read_text()
        if "exit=0" not in log:
            fail(f"successful exit marker missing from output log: {target['module']}")
        observed_axioms = []
        for theorem, axioms_text in AXIOM_RE.findall(log):
            axioms = [item.strip() for item in axioms_text.split(",") if item.strip()]
            if "sorryAx" in axioms:
                fail(f"sorryAx in {target['module']}.{theorem}")
            unexpected = set(axioms) - ALLOWED_AXIOMS
            if unexpected:
                fail(f"unexpected axioms in {target['module']}.{theorem}: {sorted(unexpected)}")
            observed_axioms.append({"theorem": theorem, "axioms": axioms})
        if observed_axioms != target["axiom_declarations"]:
            fail(f"#print axioms mismatch: {target['module']}")
        if len(observed_axioms) != target["axiom_count"]:
            fail(f"axiom declaration count mismatch: {target['module']}")
        source_axiom_prints = len(re.findall(r"^#print\s+axioms\b", source.read_text(), re.M))
        if source_axiom_prints != target["axiom_count"]:
            fail(f"source/output #print axioms count mismatch: {target['module']}")
        if "sorryAx" in log:
            fail(f"sorryAx text in successful output log: {target['module']}")

    if object_archive is not None:
        object_archive.close()
    print(
        f"OK: {len(manifest['targets'])} green targets; "
        f"{len(manifest['dependency_sources'])} source/object entries; "
        f"capture HEAD {head}; no sorryAx"
    )


if __name__ == "__main__":
    try:
        main()
    except (KeyError, ValueError, json.JSONDecodeError) as error:
        fail(f"malformed manifest/evidence: {error}")
