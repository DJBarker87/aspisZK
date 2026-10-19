#!/usr/bin/env python3
"""One exact-production-cut extraction; mandatory cgroup, no dependencies or Lean."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import signal
import subprocess
import time
import tomllib

sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
p = argparse.ArgumentParser()
p.add_argument("workspace", type=Path)
p.add_argument("tool_inventory", type=Path)
p.add_argument("--attempt", default="source-a")
args = p.parse_args()
root = args.workspace.resolve()
tool_file = args.tool_inventory.resolve()
assert sha(tool_file) == "b3b5117fb70cda0dfe44968f0e9b2c760dd3f479dfa4b505b41ec7034d489049"
tools = json.loads(tool_file.read_text())
for item in tools["tools"].values():
    assert sha(Path(item["path"])) == item["sha256"], item["path"]
for path, digest in tools["rust_runtime_binaries"].items():
    assert sha(Path(path)) == digest, path
for path, item in tools["host_dynamic_libraries"].items():
    assert sha(Path(path)) == item["sha256"], path
out = root / "runs" / args.attempt
out.mkdir(parents=True, exist_ok=False)
shutil.copytree(root / "kit", out / "source-cuts")
source = out / "source-cuts"
pins = json.loads((source / "source-pins.json").read_text())
for name, digest in pins["kit_files"].items():
    assert sha(source / name) == digest, name
assert sha(source / "prepare.py") == pins["prepare_script_sha256"]
assert not any("dependencies" in k for k in tomllib.loads((source / "Cargo.toml").read_text()))
assert len(tomllib.loads((source / "Cargo.lock").read_text())["package"]) == 1
shutil.copy2(tool_file, out / "tool-inventory.json")
shutil.copy2(Path(__file__), out / "runner.py")
cgroup = Path("/sys/fs/cgroup") / next(s.split(":", 2)[2] for s in Path("/proc/self/cgroup").read_text().splitlines() if s.startswith("0::")).lstrip("/")
read = lambda name: (cgroup / name).read_text().strip()
limits = {k: read(k) for k in ["memory.high", "memory.max", "memory.swap.max"]}
assert limits == {"memory.high": "6442450944", "memory.max": "8589934592", "memory.swap.max": "0"}, limits
sysroot = Path("/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu")
env = dict(os.environ)
for k in ["RUSTC", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER", "RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "RUSTDOCFLAGS", "CARGO_BUILD_TARGET", "CHARON_TOOLCHAIN_IS_IN_PATH"]:
    env.pop(k, None)
extra = {"PATH": str(sysroot / "bin") + ":/home/dombarker/.cargo/bin:/usr/bin:/bin",
         "LD_LIBRARY_PATH": str(sysroot / "lib"), "RUSTUP_TOOLCHAIN": "nightly-2026-06-01",
         "CARGO_BUILD_JOBS": "1", "CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS": "true",
         "CARGO_TARGET_DIR": str(root / "cargo-target"), "CARGO_NET_OFFLINE": "true", "NO_DNA": "1"}
env.update(extra)
(out / "environment.json").write_text(json.dumps(extra, indent=2) + "\n")
(out / "preflight.json").write_text(json.dumps({
    "classification": "exact migrated production cuts; no Rust/compiler/syscall refinement claim",
    "source_revision": pins["source_revision"], "source_cut_sha256": sha(source / "lib.rs"),
    "cgroup": str(cgroup), "limits": limits, "events_before": read("memory.events"),
    "tool_inventory_sha256": sha(tool_file), "runner_sha256": sha(Path(__file__)),
    "source_pins_sha256": sha(source / "source-pins.json"), "timeout_seconds_per_tool": 180,
    "expected_work": "dependency-free exact-cut crate extraction and translation; no caller/dependency/Lean build",
}, indent=2) + "\n")
records = []
def run(name, command):
    cmd = [str(x) for x in command]
    start = time.monotonic()
    peak = 0
    timed_out = False
    with (out / (name + ".log")).open("w") as log:
        child = subprocess.Popen(["/usr/bin/time", "-v", "-o", str(out / (name + ".time.log")), *cmd],
                                 cwd=source, env=env, stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
        while child.poll() is None:
            peak = max(peak, int(read("memory.current")))
            if time.monotonic() - start > 180:
                timed_out = True
                os.killpg(child.pid, signal.SIGKILL)
                break
            time.sleep(0.1)
        child.wait()
    receipt = {"name": name, "command": cmd, "exit": child.returncode, "wall_seconds": time.monotonic()-start,
               "sampled_cgroup_bytes": peak, "cgroup_peak_bytes": int(read("memory.peak")),
               "swap_current_bytes": int(read("memory.swap.current")), "events_after": read("memory.events"),
               "timed_out": timed_out, "axioms": "not checked; extraction feasibility only, no Lean run"}
    records.append(receipt)
    (out / "commands.json").write_text(json.dumps(records, indent=2) + "\n")
    print(json.dumps(receipt), flush=True)
    if child.returncode:
        print((out / (name + ".log")).read_text()[-7000:], flush=True)
        raise SystemExit(child.returncode)

charon = Path(tools["tools"]["charon"]["path"])
aeneas = Path(tools["tools"]["aeneas"]["path"])
try:
    run("charon-version", [charon, "version"])
    run("aeneas-version", [aeneas, "-version"])
    run("rustc-version", [sysroot / "bin/rustc", "-Vv"])
    run("charon", [charon, "cargo", "--preset", "aeneas", "--mir", "built", "--sysroot", "default",
                   "--include", "core::result::Result", *[arg for root_name in pins["roots"] for arg in ["--start-from", root_name]],
                   "--dest-file", out / "DigestSource.llbc",
                   "--", "--locked", "--offline", "--release", "--lib", "--no-default-features", "--features", "private-leaf-salts", "--jobs", "1"])
    llbc = json.loads((out / "DigestSource.llbc").read_text())
    assert not llbc["has_errors"] and llbc["translated"]["ordered_decls"]
    translated = llbc["translated"]
    wanted = {"new", "state", "next_row", "sample_block_validated", "source_new", "source_step", "source_inspect"}
    found = {f["item_meta"]["name"][-1]["Ident"][0]: f["def_id"]
             for f in translated["fun_decls"] if f is not None
             and f["item_meta"]["name"][-1].get("Ident", [None])[0] in wanted
             and f["item_meta"]["name"][0].get("Ident", [None])[0] == "aspis_r1_digest_source"}
    assert set(found) == wanted, found
    ordered_fun_ids = []
    for group in translated["ordered_decls"]:
        if "Fun" in group:
            value = group["Fun"]
            ordered_fun_ids.extend([value["NonRec"]] if "NonRec" in value else value["Rec"])
    assert set(found.values()) <= set(ordered_fun_ids), (found, ordered_fun_ids)
    for ident in found.values():
        f = next(f for f in translated["fun_decls"] if f is not None and f["def_id"] == ident)
        assert f["item_meta"]["opacity"] == "Transparent" and "Structured" in f["body"]
    (out / "ordered-targets.json").write_text(json.dumps({"targets": found, "ordered_fun_ids": ordered_fun_ids}, indent=2) + "\n")
    run("aeneas", [aeneas, "-sequential", "-no-progress-bar", "-abort-on-error", "-backend", "lean",
                   "-namespace", "AspisR1DigestSource", "-dest", out / "generated",
                   "-subdir", "AspisR1DigestSource", "-split-files", "-emit-json",
                   out / "DigestSource.llbc"])
    emitted = json.loads((out / "generated/translation.json").read_text())
    emitted_names = [f["rust_name"] for f in emitted["functions"]]
    assert all(any(name.endswith(target) for name in emitted_names) for target in wanted), emitted_names
    print("PASS: four complete production methods and three extraction wrappers emitted; no Rust/compiler/syscall proof claim", flush=True)
finally:
    (out / "artifact-pins.json").write_text(json.dumps({str(f.relative_to(out)): sha(f) for f in sorted(out.rglob("*")) if f.is_file() and f.name != "artifact-pins.json"}, indent=2) + "\n")
