#!/usr/bin/env python3
"""Read/hash an explicit cache closure, then run selected Lean targets serially.

`plan` and `snapshot` never execute Lean. `run` requires an existing Linux cgroup
with MemoryHigh=6GiB, MemoryMax=8GiB, MemorySwapMax=0. No fetch, package build,
re-extraction, implicit old-object overlay, parallel Lean process, or outer flock.
Adapted from the coordinator's j1-r17-build-backend.py and focused-host.py.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time

VERSION = "4.32.0"
MATHLIB = "81a5d257c8e410db227a6665ed08f64fea08e997"
ARTIFACTS = (".olean", ".olean.private", ".olean.server", ".ir", ".ilean")
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def read(path):
    return Path(path).read_text().strip()


def dump(path, value):
    Path(path).write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def require(test, message):
    if not test:
        raise ValueError(message)


def uncomment(text):
    out, depth, i = [], 0, 0
    while i < len(text):
        if text[i:i + 2] == "/-":
            depth += 1; out.extend("  "); i += 2
        elif depth and text[i:i + 2] == "-/":
            depth -= 1; out.extend("  "); i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " "); i += 1
        elif text[i:i + 2] == "--":
            j = text.find("\n", i)
            j = len(text) if j < 0 else j
            out.extend(" " * (j - i)); i = j
        else:
            out.append(text[i]); i += 1
    return "".join(out)


def imports(path, implicit_init=False):
    text = uncomment(Path(path).read_text())
    result, has_prelude = [], False
    for line in text.splitlines():
        line = line.strip()
        if not line or line == "module":
            continue
        if line == "prelude":
            has_prelude = True
            continue
        m = re.match(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(.+)$", line)
        if m:
            for name in m[1].split():
                require(re.fullmatch(r"[A-Za-z0-9_.]+", name), "Unsupported import syntax: " + line)
                if name not in result:
                    result.append(name)
        else:
            # Lean imports belong to the leading header. Later embedded JS and
            # quoted examples can contain unrelated lines beginning with import.
            break
    if implicit_init and not has_prelude and "Init" not in result:
        result.insert(0, "Init")
    return result


def stem(name):
    require(bool(re.fullmatch(r"[A-Za-z0-9_]+(?:\.[A-Za-z0-9_]+)*", name)), "Bad module name")
    return name.replace(".", "/")


def object_header(path):
    # Current Lean release header: magic/type, 32-byte version, 40-byte commit.
    # Compare the version/commit seal with this runtime's Init.olean as well.
    with Path(path).open("rb") as f:
        data = f.read(79)
    require(data[:5] == b"olean" and len(data) == 79, "Invalid olean header: " + str(path))
    require(data[7:39].split(b"\0", 1)[0] == VERSION.encode(), "Non-4.32 object: " + str(path))
    return data[7:79].hex()


def object_pins(root, name, header):
    prefix = Path(root) / stem(name)
    main = Path(str(prefix) + ".olean")
    require(main.is_file(), "Missing object: " + str(main))
    require(object_header(main) == header, "Object compiler identity differs: " + str(main))
    return {suffix: {"path": str(Path(str(prefix) + suffix)),
                     "sha256": sha(Path(str(prefix) + suffix))}
            for suffix in ARTIFACTS if Path(str(prefix) + suffix).is_file()}


def staged(work):
    path = work / "sources/SOURCE-MANIFEST.json"
    manifest = json.loads(path.read_text())
    modules = manifest["modules"]
    positions = {name: i for i, name in enumerate(manifest["topological_order"])}
    require(len(positions) == len(modules), "Incomplete/duplicate module order")
    for name, item in modules.items():
        source = work / "sources" / item["stage_as"]
        require(item["stage_as"] == stem(name) + ".lean", "Unexpected module staging path")
        require(sha(source) == item["source_sha256"], "Staged source changed: " + name)
        require(imports(source) == item["imports"], "Manifest imports differ: " + name)
        for dep in item["imports"]:
            if dep in positions:
                require(positions[dep] < positions[name], "Non-topological manifest: " + name)
    actual = {str(p.relative_to(work / "sources")) for p in (work / "sources").rglob("*") if p.is_file()}
    expected = {item["stage_as"] for item in modules.values()} | {"SOURCE-MANIFEST.json"}
    require(actual == expected, "Source staging has missing or extra files (objects are forbidden)")
    return manifest


def selected(manifest, targets, groups):
    roots = list(targets or [])
    for group in groups or []:
        require(group in manifest["groups"], "Unknown group: " + group)
        roots.extend(manifest["groups"][group]["targets"])
    require(bool(roots), "Select --target or --group; there is no full-inventory default")
    needed = set()
    def visit(name):
        require(name in manifest["modules"], "Unknown target: " + name)
        if name in needed:
            return
        needed.add(name)
        for dep in manifest["modules"][name]["imports"]:
            if dep in manifest["modules"]:
                visit(dep)
    for root in roots:
        visit(root)
    return [name for name in manifest["topological_order"] if name in needed]


def clean_package(record):
    path = Path(record["path"]).resolve()
    require(record["tracked_modified"] is False, "Package pin is not clean")
    head = subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()
    require(head == record["rev"], "Package HEAD differs: " + str(path))
    status = subprocess.check_output(["git", "-C", str(path), "status", "--porcelain", "--untracked-files=no"], text=True)
    require(not status, "Tracked package changes: " + str(path))
    return path


def snapshot(args, manifest):
    """Observe existing sources/objects/receipts only; never invoke Lean or Lake."""
    backend, runtime = args.backend.resolve(), args.runtime.resolve()
    require(read(backend / "lean-toolchain") == "leanprover/lean4:v" + VERSION, "Wrong backend toolchain")
    packages = json.loads(args.dependency_pins.read_text())
    require(len(packages) == 9 and len({p["name"] for p in packages}) == 9, "Expected nine pinned packages")
    require(next(p["rev"] for p in packages if p["name"] == "mathlib") == MATHLIB, "Wrong Mathlib revision")
    roots = [{"name": "backend", "source": str(backend), "objects": str(backend / ".lake/build/lib/lean")}]
    for package in packages:
        root = clean_package(package)
        roots.append({"name": package["name"], "source": str(root), "objects": str(root / ".lake/build/lib/lean")})
    roots.append({"name": "runtime", "source": str(runtime / "src/lean"), "objects": str(runtime / "lib/lean")})
    if (runtime / "src/lean/lake").is_dir():
        roots.append({"name": "runtime_lake", "source": str(runtime / "src/lean/lake"), "objects": str(runtime / "lib/lean")})
    runtime_files = [runtime / "bin/lean", runtime / "bin/lake",
                     *sorted((runtime / "lib/lean").glob("libleanshared*.so"))]
    require(len(runtime_files) > 2, "Missing Linux Lean shared libraries")
    runtime_pins = {str(p): sha(p) for p in runtime_files}
    header = object_header(runtime / "lib/lean/Init.olean")
    backend_manifest = json.loads(args.backend_manifest.read_text())
    backend_sources = backend_manifest["source_sha256"]
    external, visiting = {}, set()
    def visit(name):
        if name in external:
            return
        require(name not in visiting, "External import cycle: " + name)
        visiting.add(name)
        hits = [(root, Path(root["source"]) / (stem(name) + ".lean")) for root in roots]
        hits = [(root, path) for root, path in hits if path.is_file()]
        require(len(hits) == 1, "Missing/ambiguous external source: " + name)
        root, path = hits[0]
        source_hash = sha(path)
        deps = imports(path, implicit_init=True)
        for dep in deps:
            visit(dep)
        objects = object_pins(root["objects"], name, header)
        record = {"root": root["name"], "source": str(path), "source_sha256": source_hash,
                  "imports": deps, "objects": objects}
        if root["name"] == "backend":
            relative = str(path.relative_to(backend))
            require(backend_sources.get(relative) == source_hash, "Backend final source manifest differs: " + name)
            receipt_path = args.backend_receipts / (name + ".json")
            receipt = json.loads(receipt_path.read_text())
            require(receipt["exit_status"] == 0, "Backend predecessor failed: " + name)
            require(receipt["key"]["source"] == source_hash, "Backend receipt source differs: " + name)
            require(receipt["olean_sha256"] == objects[".olean"]["sha256"], "Backend receipt object differs: " + name)
            require(str(runtime / "bin/lean") in receipt["key"]["runtime"], "Backend runtime is unpinned")
            for p, value in receipt["key"]["runtime"].items():
                require(runtime_pins.get(p) == value, "Backend runtime differs: " + name)
            internal = {dep for dep in deps if external[dep]["root"] == "backend"}
            require(set(receipt["key"]["imports"]) == internal, "Backend receipt import coverage differs: " + name)
            for dep, value in receipt["key"]["imports"].items():
                require(external[dep]["objects"][".olean"]["sha256"] == value, "Backend import object differs: " + name)
            record["build_receipt"] = {"path": str(receipt_path.resolve()), "sha256": sha(receipt_path)}
        elif root["name"] not in {"runtime", "runtime_lake"}:
            subprocess.check_call(["git", "-C", root["source"], "ls-files", "--error-unmatch",
                                   str(path.relative_to(root["source"]))], stdout=subprocess.DEVNULL)
        external[name] = record
        visiting.remove(name)
    for name in ["Init", *manifest["external_import_boundary"]]:
        visit(name)
    result = {"format": 1, "captured_utc": datetime.now(timezone.utc).isoformat(),
              "lean_version": VERSION, "runtime_root": str(runtime), "runtime_files": runtime_pins,
              "olean_header_seal": header, "lake_cwd": str(backend), "roots": roots,
              "packages": packages, "modules": external,
              "provenance_files": {str(p.resolve()): sha(p) for p in
                  [args.dependency_pins, args.backend_manifest, backend / "lean-toolchain", backend / "lake-manifest.json"]},
              "scope": "Read/hash closure snapshot; cached package source/object reproducibility is not newly proved. Backend objects require successful matching receipts. No Lean or package build executed."}
    require(not args.output.exists(), "Snapshot output already exists; retain it and choose another path")
    dump(args.output, result)
    print(f"SNAPSHOT {len(external)} external modules; no compiler invoked", flush=True)


def verify_snapshot(path):
    data = json.loads(path.read_text())
    require(data["lean_version"] == VERSION, "Wrong external snapshot version")
    for package in data["packages"]:
        clean_package(package)
    files = dict(data["runtime_files"])
    files.update(data["provenance_files"])
    for name, record in data["modules"].items():
        files[record["source"]] = record["source_sha256"]
        require(imports(record["source"], implicit_init=True) == record["imports"], "External imports changed: " + name)
        root = next(r for r in data["roots"] if r["name"] == record["root"])
        require(object_pins(root["objects"], name, data["olean_header_seal"]) == record["objects"], "External objects/companions changed: " + name)
        for obj in record["objects"].values():
            files[obj["path"]] = obj["sha256"]
        if "build_receipt" in record:
            r = record["build_receipt"]; files[r["path"]] = r["sha256"]
    for p, expected in files.items():
        require(sha(p) == expected, "Pinned external file changed: " + p)
    return data, {p: (Path(p).stat().st_size, Path(p).stat().st_mtime_ns) for p in files}


def external_keys(data):
    """Stable closure keys: recapturing identical evidence does not force replay."""
    keys, visiting = {}, set()
    def visit(name):
        if name in keys:
            return keys[name]
        require(name not in visiting, "External key cycle: " + name)
        visiting.add(name); item = data["modules"][name]
        key = {"source": item["source_sha256"],
               "objects": {suffix: obj["sha256"] for suffix, obj in item["objects"].items()},
               "imports": {dep: visit(dep) for dep in item["imports"]},
               "runtime": data["runtime_files"]}
        keys[name] = digest(key); visiting.remove(name)
        return keys[name]
    for name in data["modules"]:
        visit(name)
    return keys


def cgroup():
    relative = next(line.split(":", 2)[2] for line in Path("/proc/self/cgroup").read_text().splitlines() if line.startswith("0::"))
    cg = Path("/sys/fs/cgroup") / relative.lstrip("/")
    limits = {name: read(cg / name) for name in ("memory.high", "memory.max", "memory.swap.max")}
    require(limits == {"memory.high": str(6 * 2**30), "memory.max": str(8 * 2**30), "memory.swap.max": "0"}, "Mandatory 6G/8G/swap0 cgroup missing: " + repr(limits))
    return cg, limits


def audits(source, log):
    expected = len(re.findall(r"^\s*#print\s+axioms\s+", uncomment(source.read_text()), re.M))
    found = [{"declaration": name, "axioms": [s.strip() for s in values.split(",") if s.strip()]}
             for name, values in re.findall(r"'([^']+)'\s+depends on axioms:\s*\[([^\]]*)\]", log, re.S)]
    found += [{"declaration": name, "axioms": []} for name in
              re.findall(r"'([^']+)'\s+does not depend on any axioms", log)]
    passed = len(found) == expected and all(set(x["axioms"]) <= STANDARD_AXIOMS for x in found)
    return {"requested_count": expected, "reports": found, "passed": passed,
            "scope": "Only source #print axioms commands; zero requested audits makes no axiom claim."}


def import_overlay(out, external):
    """One complete namespace tree; immutable object bytes stay at pinned origins.

    Lean can select a namespace directory from the first search root rather than
    fall through for each nested module. Mixing a new AspisV8R19 module and older
    attested AspisV8R19 dependencies therefore needs a unified directory tree.
    This function adds no artifacts beyond the verified snapshot or, later,
    receipt-checked project outputs. It does not weaken any axiom audit.
    """
    overlay = out / "import-overlay"; overlay.mkdir()
    owners = {}
    journal = out / "import-overlay-links.jsonl"
    def add(name, source_sha, objects, origin):
        identity = {"source_sha256": source_sha,
                    "objects": {suffix: item["sha256"] for suffix, item in objects.items()}}
        if name in owners:
            require(owners[name] == identity, "Conflicting overlay module/object hashes: " + name)
            return
        owners[name] = identity
        with journal.open("a") as log:
            for suffix, item in objects.items():
                source = Path(item["path"])
                destination = overlay / (stem(name) + suffix)
                require(not destination.exists() and not destination.is_symlink(),
                        "Conflicting overlay destination: " + str(destination))
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.symlink_to(source.resolve())
                log.write(json.dumps({"module": name, "suffix": suffix,
                    "source": str(source), "resolved_source": str(source.resolve()),
                    "destination": str(destination), "sha256": item["sha256"],
                    "source_lean_sha256": source_sha, "origin": origin}, sort_keys=True) + "\n")
    for name, record in external["modules"].items():
        add(name, record["source_sha256"], record["objects"], "verified external snapshot")
    return overlay, add


def run(args, manifest):
    work = args.workspace.resolve(); ordered = selected(manifest, args.target, args.group)
    cg, limits = cgroup()
    external, file_stats = verify_snapshot(args.external_snapshot)
    external_key = external_keys(external)
    runtime = Path(external["runtime_root"])
    version = subprocess.check_output([str(runtime / "bin/lean"), "--version"], text=True).strip()
    require("version " + VERSION + "," in version, "Wrong Lean runtime")
    require(re.fullmatch(r"[A-Za-z0-9_.-]+", args.attempt), "Invalid attempt label")
    out = work / "runs" / args.attempt; out.mkdir(parents=True, exist_ok=False)
    shutil.copy2(__file__, out / "runner.py")
    shutil.copy2(args.external_snapshot, out / "external-inputs.json")
    objects, saved = work / "objects", work / "successful-targets"
    objects.mkdir(exist_ok=True); saved.mkdir(exist_ok=True)
    allowed_objects = {stem(name) + suffix for name in manifest["modules"] for suffix in ARTIFACTS}
    for path in objects.rglob("*"):
        if path.is_file():
            require(str(path.relative_to(objects)) in allowed_objects,
                    "Unattested/shadowing file in project object root: " + str(path))
    overlay, add_overlay = import_overlay(out, external)
    roots = list(dict.fromkeys([str(overlay), str(objects), *[r["objects"] for r in external["roots"]]]))
    require(all("4.31" not in path for path in roots), "Forbidden old toolchain search root")
    dump(out / "preflight.json", {"ordered_modules": ordered, "limits": limits, "cgroup": str(cg),
        "lean_version": version, "source_revision": args.revision,
        "source_manifest_sha256": sha(work / "sources/SOURCE-MANIFEST.json"),
        "external_snapshot_sha256": sha(args.external_snapshot), "explicit_search_roots": roots,
        "runner_sha256": sha(Path(__file__)), "started_utc": datetime.now(timezone.utc).isoformat()})
    completed = {}; reused = []
    for name in ordered:
        for p, stat in file_stats.items():
            require((Path(p).stat().st_size, Path(p).stat().st_mtime_ns) == stat, "External input changed during serial run: " + p)
        item = manifest["modules"][name]; source = work / "sources" / item["stage_as"]
        require(sha(source) == item["source_sha256"], "Source changed during run: " + name)
        depkeys = {}
        for dep in imports(source, implicit_init=True):
            if dep in manifest["modules"]:
                require(dep in completed, "Missing completed predecessor: " + dep)
                depkeys[dep] = {"receipt_key": digest(completed[dep]["key"]),
                               "objects": object_pins(objects, dep, external["olean_header_seal"])}
            else:
                require(dep in external["modules"], "External snapshot lacks: " + dep)
                depkeys[dep] = {"objects": external["modules"][dep]["objects"],
                               "closure_key": external_key[dep]}
        key = {"source_sha256": sha(source), "imports": depkeys,
               "runtime": external["runtime_files"], "options": ["-j1", "-M0"], "cache_protocol": 1}
        previous = saved / (name + ".json")
        if previous.is_file():
            old = json.loads(previous.read_text())
            if (old.get("key") == key and old.get("exit_status") == 0 and old.get("axioms", {}).get("passed")
                    and (objects / (stem(name) + ".olean")).is_file()):
                current = object_pins(objects, name, external["olean_header_seal"])
                if current == old["objects"]:
                    completed[name] = old; reused.append(name)
                    add_overlay(name, sha(source), current, "exact successful receipt reuse")
                    print("REUSE " + name, flush=True); continue
        target = out / name; target.mkdir()
        shutil.copy2(source, target / "source.lean")
        artifact_root = target / "artifacts"; obj = artifact_root / (stem(name) + ".olean")
        obj.parent.mkdir(parents=True)
        cmd = ["/usr/bin/time", "-v", "-o", str(target / "time.log"), str(runtime / "bin/lake"),
               "--no-cache", "env", "python3", str(Path(__file__).resolve()), "--exec-lean",
               str(runtime / "bin/lean"), os.pathsep.join(roots), "-j1", "-M0", "-R", str(work / "sources"),
               "-o", str(obj), str(source)]
        env = {k: v for k, v in os.environ.items() if k not in {"LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"}}
        before = read(cg / "memory.events"); begin = time.monotonic(); peak = 0; stopped = False
        dump(target / "preflight.json", {"target": name, "source_revision": args.revision,
            "source_manifest_entry": item, "key": key, "command": cmd, "cwd": external["lake_cwd"],
            "external_snapshot_sha256": sha(args.external_snapshot), "limits": limits, "cgroup": str(cg),
            "memory_events_before": before, "started_utc": datetime.now(timezone.utc).isoformat()})
        print("START " + name, flush=True)
        with (target / "lean.log").open("w") as log:
            proc = subprocess.Popen(cmd, cwd=external["lake_cwd"], env=env,
                                    stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
            while proc.poll() is None:
                peak = max(peak, int(read(cg / "memory.current")))
                if time.monotonic() - begin >= 600:
                    os.killpg(proc.pid, signal.SIGKILL); stopped = True; break
                time.sleep(0.2)
            rc = proc.wait()
        log = (target / "lean.log").read_text(); audit = audits(source, log)
        receipt = {"target": name, "source_revision": args.revision, "source_manifest_entry": item,
                   "key": key, "command": cmd, "cwd": external["lake_cwd"], "exit_status": rc,
                   "wall_seconds": round(time.monotonic() - begin, 3), "sampled_cgroup_peak_bytes": peak,
                   "cgroup_memory_peak_cumulative": read(cg / "memory.peak"),
                   "cgroup_swap_current": read(cg / "memory.swap.current"), "limits": limits,
                   "memory_events_before": before, "memory_events_after": read(cg / "memory.events"),
                   "stopped_at_ten_minutes_without_target": stopped, "axioms": audit,
                   "dependency_build": False, "backend_build": False}
        timing = (target / "time.log").read_text()
        for field, label in [("peak_process_rss_kib", "Maximum resident set size (kbytes)"), ("process_swaps", "Swaps")]:
            match = re.search(re.escape(label) + r":\s*(\d+)", timing)
            receipt[field] = int(match[1]) if match else None
        dump(target / "receipt.json", receipt); dump(target / "axioms.json", audit)
        print(f"END {name} exit={rc} audit={audit['passed']} wall={receipt['wall_seconds']} cgroup_peak={peak}", flush=True)
        if rc != 0 or not audit["passed"]:
            print(log[-12000:], flush=True)
            return rc or 1
        fresh = object_pins(artifact_root, name, external["olean_header_seal"])
        # A changed compile must not retain a companion absent from the new output.
        for suffix in set(ARTIFACTS) - set(fresh):
            stale = objects / (stem(name) + suffix)
            require(not stale.exists(), "Stale extra companion; quarantine explicitly before retry: " + str(stale))
        for suffix, artifact in fresh.items():
            destination = objects / (stem(name) + suffix); destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(artifact["path"], destination)
        receipt["objects"] = object_pins(objects, name, external["olean_header_seal"])
        dump(target / "receipt.json", receipt); dump(previous, receipt); completed[name] = receipt
        add_overlay(name, sha(source), receipt["objects"], "new successful compile and axiom audit")
    dump(out / "complete.json", {"targets": ordered, "reused": reused, "exit_status": 0})
    return 0


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "--exec-lean":
        env = dict(os.environ); env["LEAN_PATH"] = sys.argv[3]
        env.pop("LEAN_SRC_PATH", None); env.pop("LEAN_SYSROOT", None)
        os.execve(sys.argv[2], [sys.argv[2], *sys.argv[4:]], env)
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["plan", "snapshot", "run"])
    ap.add_argument("workspace", type=Path, help="Has sources/SOURCE-MANIFEST.json and module-name .lean staging")
    ap.add_argument("--target", action="append"); ap.add_argument("--group", action="append")
    ap.add_argument("--backend", type=Path); ap.add_argument("--runtime", type=Path)
    ap.add_argument("--dependency-pins", type=Path); ap.add_argument("--backend-manifest", type=Path)
    ap.add_argument("--backend-receipts", type=Path); ap.add_argument("--output", type=Path)
    ap.add_argument("--external-snapshot", type=Path); ap.add_argument("--attempt"); ap.add_argument("--revision")
    args = ap.parse_args(); args.workspace = args.workspace.resolve()
    manifest = staged(args.workspace)
    if args.mode == "plan":
        print(json.dumps(selected(manifest, args.target, args.group), indent=2)); return 0
    if args.mode == "snapshot":
        require(all([args.backend, args.runtime, args.dependency_pins, args.backend_manifest,
                     args.backend_receipts, args.output]), "Snapshot inputs are required")
        snapshot(args, manifest); return 0
    require(all([args.external_snapshot, args.attempt, args.revision]), "Run inputs are required")
    return run(args, manifest)


if __name__ == "__main__":
    sys.exit(main())
