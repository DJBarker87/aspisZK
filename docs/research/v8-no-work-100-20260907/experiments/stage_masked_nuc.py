#!/usr/bin/env python3
"""Build an exact research/borrowed import overlay and provenance manifest.

Metadata/source/archive preparation only; never invokes a compiler. Native
mathlib/third-party artifacts remain a declared pinned-revision cache boundary,
not a claimed full compilation replay or transitive source/artifact audit.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tarfile
import tempfile

EX = Path(__file__).resolve().parent
REPO = Path(subprocess.check_output(["git", "-C", str(EX), "rev-parse", "--show-toplevel"], text=True).strip())
CACHE = Path("/Users/dominic/ZK/AspisFormal")
MATH = CACHE / ".lake/packages/mathlib"
BASE = "b006d34ffc6d552cd5ecd9f292cf2bd095f7fdb9"
BORROWED = "26a9cd4718aae9f9de7ef1c3394fb74a229085d5"
MATHPIN = "81a5d257c8e410db227a6665ed08f64fea08e997"
PENDING = {"MaskedCurveRepresentation", "SelectedMaskedCurveTail", "SelectedSupportIdentification", "OffFamilyIntersection", "TwoTailQueryBound", "SelectedOutsideQuery", "FixedC1OutsideQuery"}
NEW_GREEN = {
    "MaskedCurveTail": ("87faa696677db638b53d1258aa9ba8b4971d983255e15e658e5b14bc9df57158", "a2e13cff44d43debdb5044b225986f9bafb0c1848829b694797172183dc2c7af"),
    "HighAgreementTail": ("740170c9447e45f6a18626332cfd873d7bfeb7ea52b46c85e9c44e700bc06db5", "ae4194137cd026c25ce4bd1c8cfc3a8efccf538e71cafc6c8a39924934aafaa0"),
}


def tree(repo, revision):
    raw = subprocess.check_output(["git", "-C", str(repo), "ls-tree", "-r", revision], text=True)
    return {line.split("\t", 1)[1]: line.split()[2] for line in raw.splitlines()}


def sha(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def blob(data):
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def imports(data):
    """Ignore nested Lean block comments, line comments and string literals."""
    text = data.decode()
    clean = []
    i, depth = 0, 0
    while i < len(text):
        pair = text[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                i += 2
            else:
                clean.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif pair == "/-":
            depth = 1
            clean.append(" ")
            i += 2
        elif pair == "--":
            while i < len(text) and text[i] != "\n":
                i += 1
        elif text[i] == '"':
            clean.append(" ")
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    clean.append("\n" if text[i] == "\n" else " ")
                    i += 1
        else:
            clean.append(text[i])
            i += 1
    return re.findall(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([A-Za-z0-9_.]+)", "".join(clean), re.M)


def main():
    assert sys.argv[1:]
    assert subprocess.check_output(["git", "-C", str(MATH), "rev-parse", "HEAD"], text=True).strip() == MATHPIN
    packages = {p["name"]: p["rev"] for p in json.loads((CACHE / "lake-manifest.json").read_text())["packages"]}
    trees = {"research": tree(REPO, BASE), "borrowed": tree(REPO, BORROWED)}
    pending = list(sys.argv[1:])
    visited = set()
    entries = []
    count = {"research": 0, "borrowed": 0, "package": 0}
    staging = Path(tempfile.mkdtemp(prefix="aspis-masked-nuc-"))
    while pending:
        module = pending.pop()
        if module in visited or module.split(".")[0] in {"Lean", "Init", "Std", "Lake"}:
            continue
        visited.add(module)
        relative = module.replace(".", "/")
        package = None
        for name, revision in packages.items():
            package_root = CACHE / ".lake/packages" / name
            if (package_root / (relative + ".lean")).exists():
                package = name
                break
        if module.startswith("AspisFormal."):
            category = "borrowed"
            source = CACHE / (relative + ".lean")
            olean = CACHE / ".lake/build/lib/lean" / (relative + ".olean")
            tracked = "AspisFormal/" + relative + ".lean"
        elif package is not None:
            # Reuse the NUC's native pinned package cache as a declared
            # compiler/cache boundary; this is not a package-wide replay.
            count["package"] += 1
            continue
        else:
            category = "research"
            source = EX / (module + ".lean")
            olean = EX / (module + ".olean")
            for alternate in (Path("/tmp/aspis-v8-near-gamma-cache"), Path("/tmp/aspis-v8-joint-cache.n3hmg5")):
                if not olean.exists():
                    olean = alternate / (module + ".olean")
            tracked = "docs/research/v8-no-work-100-20260907/experiments/" + module + ".lean"
        data = source.read_bytes()
        if module not in PENDING and module not in NEW_GREEN:
            assert blob(data) == trees[package if category == "package" else category].get(tracked), ("source pin mismatch", module, tracked)
        if module in NEW_GREEN:
            assert sha(source) == NEW_GREEN[module][0] and sha(olean) == NEW_GREEN[module][1], module
        count[category] += 1
        pending.extend(imports(data))
        candidates = [(source, relative + ".lean", "source")]
        if module not in PENDING:
            assert olean.exists(), ("missing compiled import", module, olean)
            candidates.append((olean, relative + ".olean", "olean"))
            for suffix in (".private", ".server"):
                part = Path(str(olean) + suffix)
                if part.exists():
                    candidates.append((part, relative + ".olean" + suffix, "olean" + suffix))
        for path, destination, kind in candidates:
            remote = (f".lake/packages/{package}/" if category == "package" and kind == "source"
                      else f".lake/packages/{package}/.lake/build/lib/lean/" if category == "package"
                      else None)
            entries.append({"module": module, "category": category, "kind": kind,
                            "package": package if category == "package" else None,
                            "local": str(path), "overlay": destination,
                            "remote_cache": None if remote is None else remote + destination,
                            "sha256": sha(path), "bytes": path.stat().st_size})
    manifest = {"research": BASE, "borrowed": BORROWED, "mathlib": MATHPIN,
                "lean_commit": "8c9756b28d64dab099da31a4c09229a9e6a2ef35", "packages": packages,
                "targets": sys.argv[1:], "pending_no_olean": sorted(PENDING),
                "counts": count, "files": entries}
    manifest_path = staging / "manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    archive = staging / "overlay.tar"
    with tarfile.open(archive, "w") as bundle:
        bundle.add(manifest_path, arcname="manifest.json")
        for entry in entries:
            if entry["category"] != "package":
                bundle.add(entry["local"], arcname="overlay/" + entry["overlay"])
    print(json.dumps({"staging": str(staging), "archive": str(archive),
                      "manifest": str(manifest_path), "counts": count,
                      "files": len(entries), "archive_bytes": archive.stat().st_size,
                      "archive_sha256": sha(archive)}, indent=2))


if __name__ == "__main__":
    main()
