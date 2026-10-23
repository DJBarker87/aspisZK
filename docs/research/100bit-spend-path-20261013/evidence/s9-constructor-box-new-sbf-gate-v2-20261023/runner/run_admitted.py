from pathlib import Path
import contextlib, fcntl, hashlib, io, json, os, runpy, subprocess, sys, time
W = Path(__file__).resolve().parent
G = 1024**3
high, cap, reserve = 3*G, 4*G, 8*G
root = Path("/home/dombarker/project-offloads/s9-actual-weights-new-sbf-candidate-v1-20261023/repo-v2")
target = Path("/home/dombarker/project-offloads/s9-actual-weights-new-sbf-candidate-v1-20261023/target-warm-copy")
out = Path("/home/dombarker/project-offloads/s9-actual-weights-new-sbf-candidate-v1-20261023/artifacts/sbf-v2")
collector = Path("/home/dombarker/project-offloads/r1-circle-sample-wrapper-extraction-v2/collect-cgroups.py")
lockpath = Path("/tmp/aspis-global-extraction-admission-20261019.lock")
cargo_sbf = Path("/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf")
weights = root / "crates/aspis-r1-cost-probe/src/weights.rs"
lockfile = root / "Cargo.lock"
expected_weights = "c14801d8872e4faa64660dc925ab49e10ff44e1cb2d5483643c8d8ce052e0b80"
expected_lock = "5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef"
assert hashlib.sha256(weights.read_bytes()).hexdigest() == expected_weights
assert hashlib.sha256(lockfile.read_bytes()).hexdigest() == expected_lock
assert not out.exists(), f"refusing existing output {out}"
out.mkdir(parents=True)
args = [str(cargo_sbf), "--manifest-path", str(root/"programs/r1-cost-probe/Cargo.toml"), "--sbf-out-dir", str(out), "--features", "pool-adapter,private-leaf-salts", "--skip-tools-install", "--offline", "-j", "1", "--", "--locked"]
with lockpath.open("a") as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf): runpy.run_path(str(collector))
    inv = json.loads(buf.getvalue())
    rows = inv["all_populated_cgroups"]
    unc = [r for r in rows if r["max"] == "max" and (r["scope"] or (Path(r["path"]).name.endswith(".service") and not any(Path(r["path"]) in Path(s["path"]).parents for s in rows)))]
    outer = [r for r in unc if not any(Path(s["path"]) in Path(r["path"]).parents for s in unc)]
    usage, items = 0, []
    for r in outer:
        p = Path(r["path"]); cur = int(r["current_bytes"] or 0); sw = 0; clean = 0
        try:
            cur = max(cur, int((p/"memory.current").read_text()))
            stats = {k:int(v) for k,v in (x.split() for x in (p/"memory.stat").read_text().splitlines())}
            sw = int((p/"memory.swap.current").read_text())
            clean = max(0, min(cur, stats.get("inactive_file",0), stats.get("file",0))-stats.get("file_dirty",0)-stats.get("file_writeback",0))
        except (FileNotFoundError, ValueError): pass
        charged = cur-clean+sw; usage += charged; items.append({"path":str(p),"charged_bytes":charged})
    finite = int(inv["effective_sum_bytes"]); total = int(inv["MemTotal_kB"])*1024; avail = int(inv["MemAvailable_kB"])*1024
    checks = {"finite_plus_cap_le_48GiB":finite+cap<=48*G,"finite_cap_usage_reserve_le_memtotal":finite+cap+usage+reserve<=total,"available_after_cap_reserve_ge_14GiB":avail-cap>=14*G}
    admission = {"phase":"optimized_sbf_constructor_gate","inventory":inv,"uncapped_outer_charged":items,"uncapped_charged_bytes":usage,"scope_high_bytes":high,"scope_max_bytes":cap,"swap_max_bytes":0,"os_reserve_bytes":reserve,"checks":checks}
    (W/"admission.json").write_text(json.dumps(admission,indent=2)+"\n")
    print(json.dumps({"checks":checks,"finite_GiB":finite/G,"uncapped_charged_GiB":usage/G,"MemAvailable_GiB":avail/G}),flush=True)
    assert all(checks.values()), "admission denied; no child launched"
    unit = f"s9-constructor-sbf-{os.getpid()}-{time.time_ns()}"
    env = ["/usr/bin/env", "PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin", f"CARGO_TARGET_DIR={target}", "CARGO_NET_OFFLINE=true", "CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS=-C link-arg=--threads=4", "/usr/bin/time", "-v", "-o", str(W/"time.log"), *args]
    cmd = ["systemd-run","--user","--scope","--quiet","--unit="+unit,"-p",f"MemoryHigh={high}","-p",f"MemoryMax={cap}","-p","MemorySwapMax=0","-p","TasksMax=128",*env]
    start = time.time_ns()
    proc = subprocess.Popen(cmd,cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    deadline = time.monotonic()+20; control = None; limits = None
    while time.monotonic()<deadline:
        if proc.poll() is not None: break
        show = subprocess.run(["systemctl","--user","show",unit+".scope","--property=ControlGroup","--value"],text=True,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL)
        group = show.stdout.strip()
        if show.returncode==0 and group:
            cg=Path("/sys/fs/cgroup")/group.lstrip("/")
            try:
                limits={k:(cg/k).read_text().strip() for k in ("memory.high","memory.max","memory.swap.max")}
                populated="populated 1" in (cg/"cgroup.events").read_text()
            except FileNotFoundError: time.sleep(.05); continue
            if limits=={"memory.high":str(high),"memory.max":str(cap),"memory.swap.max":"0"} and populated:
                control=group; break
        time.sleep(.05)
    assert control is not None or proc.poll() is not None, "scope did not become verifiably populated/capped"
    metadata = {"task":"optimized SBF stack feasibility only; no fixtures/CU gate","source_revision":"e668ce58d31bde2fe25d8c6e76eba2262fad9e96","weights_sha256":expected_weights,"cargo_lock_sha256":expected_lock,"argv":args,"cwd":str(root),"target_dir":str(target),"target_cache_origin":"copied unchanged from /home/dombarker/project-offloads/aspis-r1-p2-20261010/target; isolated copy; source/lock differ and Cargo fingerprints will validate/rebuild","cargo_build_sbf":str(cargo_sbf),"tool_version":subprocess.run([str(cargo_sbf),"--version"],capture_output=True,text=True).stdout.strip(),"unit":unit+".scope","control_group":control,"actual_limits":limits,"started_unix_ns":start}
    (W/"command.json").write_text(json.dumps(metadata,indent=2)+"\n")
    fcntl.flock(lock,fcntl.LOCK_UN)
    out_text,_=proc.communicate(); (W/"build.log").write_text(out_text)
    finish=time.time_ns(); rc=proc.returncode
    peak=None
    if control:
        try: peak=(Path("/sys/fs/cgroup")/control.lstrip("/")/"memory.peak").read_text().strip()
        except FileNotFoundError: pass
    receipt={**metadata,"finished_unix_ns":finish,"wall_seconds":(finish-start)/1e9,"exit_status":rc,"memory_peak_bytes":peak,"time_report_path":str(W/"time.log"),"build_log_path":str(W/"build.log")}
    (W/"receipt.json").write_text(json.dumps(receipt,indent=2)+"\n")
    print(out_text[-5000:],end="")
    print(f"EXIT_STATUS={rc}")
    raise SystemExit(rc)
