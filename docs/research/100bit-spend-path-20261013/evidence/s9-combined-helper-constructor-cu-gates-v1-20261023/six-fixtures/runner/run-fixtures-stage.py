from pathlib import Path
import hashlib, json, os, re, subprocess, time

W = Path(__file__).resolve().parent
RUN = W.parent
G = 1024 ** 3
CG = Path("/sys/fs/cgroup") / Path("/proc/self/cgroup").read_text().strip().removeprefix("0::").lstrip("/")
limits = {k: (CG / k).read_text().strip() for k in ("memory.high", "memory.max", "memory.swap.max")}
assert limits == {"memory.high": str(2 * G), "memory.max": str(4 * G), "memory.swap.max": "0"}, limits

sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
src = RUN / "work/src"
artifact = RUN / "artifacts/aspis_r1_cost_probe_program.so"
manifest = src / "s9-candidate-source-manifest.json"
build = json.loads((RUN / "gates/sbf/receipt.json").read_text())
stack = json.loads((RUN / "gates/sbf/stack-audit.json").read_text())
doc = json.loads(manifest.read_text())
assert sha(artifact) == "603af510fca0a54209d6950d814256af257cb8da4e239bbb73e25e01daeb64a2"
assert sha(artifact) == build["candidate_artifact_sha256"] == stack["candidate_artifact_sha256"]
assert stack["constructor_stack_diagnostic"] is False
assert stack["pack_helper_stack_diagnostic"] is False
assert stack["constructor_calls_out_of_line_pack_helper"] is True
assert stack["whole_program_stack_diagnostic_count"] == 34
assert {rel: sha(src / rel) for rel in doc["files"]} == doc["files"], "candidate source differs from admitted SBF build"

baseline_runs = W / "baseline-runs.json"
baseline_cu = W / "baseline-cu.json"
prior = W / "prior-helper933-gate-result.json"
assert sha(baseline_runs) == "a1b0a795f5101751950e42c7db19a1decfa3bd7f61d8ef37c85b211fa11a749f"
assert sha(baseline_cu) == "a86721fad52e8b16fe3b1e8f6061ac2b1a6923ec730d7f24d50c601d294a473d"
assert sha(prior) == "73005b1485ef3ad6ddca5dcfcc755aa154611cecbdfa89e3508002da26cec6b1"
previous = json.loads(prior.read_text())
assert previous["candidate_artifact_sha256"] == "5aac14ef69f482c8b3bc95a400c321288b6a27f2b5b96adabcd21ad0c41019eb"
old_rows = {r["fixture"]: r for r in previous["six_fixture_rows"]}
cases = [x for x in json.loads(baseline_runs.read_text()) if x["name"].startswith("cu-")]
b1_rows = {x["fixture"]: x for x in json.loads(baseline_cu.read_text())}
assert len(cases) == len(b1_rows) == len(old_rows) == 6

E = RUN / "gates/fixtures-v2"
E.mkdir(parents=True, exist_ok=False)
rows = []
env = dict(os.environ)
env["PATH"] = "/home/dombarker/.cargo/bin:/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin:/usr/bin:/bin"
gate = Path("/home/dombarker/project-offloads/codex-r1-format-adopt-20261019/artifacts/pool_gate_adopt")
for case in cases:
    name = case["name"]
    fixture = name.removeprefix("cu-")
    cmd = case["command"].copy()
    baseline = json.loads(Path(cmd[4]).read_text())
    out = RUN / "runs-v2" / name
    out.mkdir(parents=True, exist_ok=False)
    cmd[0] = str(gate)
    cmd[2] = str(artifact)
    cmd[4] = str(out / "evidence.json")
    cmd[5] = str(out / "task")
    input_hashes = {"pool_so": sha(Path(cmd[1])), "candidate_so": sha(Path(cmd[2])),
                    "registry_so": sha(Path(cmd[3])), "proof": sha(Path(cmd[11])),
                    "public_asf": sha(Path(cmd[12]))}
    folder = E / name
    folder.mkdir(parents=True, exist_ok=False)
    (folder / "command.json").write_text(json.dumps({
        "argv": cmd, "cwd": "/home/dombarker/project-offloads/codex-cx-pin-20261020",
        "candidate_artifact_sha256": sha(artifact), "source_manifest_sha256": sha(manifest),
        "baseline_runs_sha256": sha(baseline_runs), "baseline_cu_sha256": sha(baseline_cu),
        "prior_helper933_gate_sha256": sha(prior), "input_artifact_and_proof_sha256": input_hashes,
        "timeout_seconds": 60}, indent=2) + "\n")
    before = (CG / "memory.events").read_text()
    start = time.monotonic()
    timed_out = False
    with (folder / "output.log").open("x") as log:
        try:
            result = subprocess.run(["/usr/bin/time", "-v", "-o", str(folder / "time.log"), *cmd],
                                    cwd="/home/dombarker/project-offloads/codex-cx-pin-20261020",
                                    env=env, stdout=log, stderr=subprocess.STDOUT, timeout=60)
            status = result.returncode
        except subprocess.TimeoutExpired:
            status = 124
            timed_out = True
    timing = (folder / "time.log").read_text() if (folder / "time.log").exists() else ""
    rss = re.search(r"Maximum resident set size \(kbytes\):\s*(\d+)", timing)
    receipt = {"name": name, "exit_status": status, "timed_out": timed_out,
               "wall_seconds": round(time.monotonic() - start, 3),
               "peak_process_rss_kib": int(rss[1]) if rss else None,
               "scope_peak_bytes": int((CG / "memory.peak").read_text()),
               "swap_current_bytes": int((CG / "memory.swap.current").read_text()),
               "memory_events_before": before, "memory_events_after": (CG / "memory.events").read_text(),
               "limits": limits, "candidate_artifact_sha256": sha(artifact)}
    (folder / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    if status != 0:
        raise SystemExit(f"fixture command failed: {name}, exit {status}")
    data = json.loads((out / "evidence.json").read_text())
    actual = data["execution"]
    expected = baseline["execution"]
    old_b1 = b1_rows[fixture]
    old_candidate = old_rows[fixture]
    stage1 = actual.get("stage1_compute_units")
    settlement = actual.get("compute_units")
    stage1_base = expected["stage1_compute_units"]
    settlement_base = expected["compute_units"]
    stage1_delta = stage1 - stage1_base if stage1 is not None else None
    settlement_delta = settlement - settlement_base if settlement is not None else None
    stage1_increment = stage1 - old_candidate["stage1_cu"] if stage1 is not None else None
    settlement_increment = settlement - old_candidate["settlement_cu"] if settlement is not None else None
    row = {"fixture": fixture, "candidate_artifact_sha256": sha(artifact),
           "input_artifact_and_proof_sha256": input_hashes, "candidate_evidence_sha256": sha(out / "evidence.json"),
           "stage1_cu": stage1, "stage1_b1_cu": old_b1["b1_stage1"], "stage1_delta_vs_b1_cu": stage1_delta,
           "stage1_b1_plus12000_pass": stage1 is not None and stage1 <= old_b1["b1_stage1"] + 12000,
           "settlement_cu": settlement, "settlement_b1_cu": old_b1["b1_settlement"],
           "settlement_delta_vs_b1_cu": settlement_delta,
           "settlement_b1_plus12000_pass": settlement is not None and settlement <= old_b1["b1_settlement"] + 12000,
           "stage1_increment_vs_helper933_cu": stage1_increment,
           "stage1_increment_headroom_cu": 1183,
           "stage1_increment_headroom_pass": stage1_increment is not None and stage1_increment <= 1183,
           "settlement_increment_vs_helper933_cu": settlement_increment,
           "settlement_increment_headroom_cu": 3901,
           "settlement_increment_headroom_pass": settlement_increment is not None and settlement_increment <= 3901,
           "legacy_strict_b1_stage1_pass": stage1 is not None and stage1 <= old_b1["b1_stage1"],
           "legacy_strict_b1_settlement_pass": settlement is not None and settlement <= old_b1["b1_settlement"],
           "stage1_checkpoint_tail_same": actual.get("stage1_checkpoint_tail_sha256") == expected["stage1_checkpoint_tail_sha256"],
           "return_data_same": actual.get("return_data_sha256") == expected["return_data_sha256"],
           "run_receipt": receipt}
    row["approved_plus12000_pass"] = row["stage1_b1_plus12000_pass"] and row["settlement_b1_plus12000_pass"]
    row["incremental_headroom_pass"] = row["stage1_increment_headroom_pass"] and row["settlement_increment_headroom_pass"]
    rows.append(row)
    print(json.dumps({"fixture": fixture, "stage1_delta_vs_b1": stage1_delta,
                      "settlement_delta_vs_b1": settlement_delta,
                      "increment_vs_helper933": [stage1_increment, settlement_increment],
                      "plus12000_pass": row["approved_plus12000_pass"],
                      "headroom_pass": row["incremental_headroom_pass"]}), flush=True)

result = {"classification": "combined S9 helper933 + constructor v2 isolated candidate; no adoption/deployment",
          "research_head": doc["research_head"], "candidate_weights_sha256": doc["candidate_weights_sha256"],
          "source_manifest_sha256": sha(manifest), "candidate_artifact_sha256": sha(artifact),
          "baseline_runs_sha256": sha(baseline_runs), "baseline_cu_sha256": sha(baseline_cu),
          "prior_helper933_gate_sha256": sha(prior), "six_fixture_rows": rows,
          "all_six_b1_plus12000_pass": all(r["approved_plus12000_pass"] for r in rows),
          "all_six_incremental_headroom_pass": all(r["incremental_headroom_pass"] for r in rows),
          "all_six_outputs_match": all(r["stage1_checkpoint_tail_same"] and r["return_data_same"] for r in rows),
          "legacy_strict_b1_all_six_pass": all(r["legacy_strict_b1_stage1_pass"] and r["legacy_strict_b1_settlement_pass"] for r in rows),
          "stack_scope": "constructor and box_from_parts own symbols checked separately; whole-program stack warnings remain",
          "limits": limits}
(RUN / "gates/cu-result-v2.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"six_fixtures": len(rows), "all_plus12000_pass": result["all_six_b1_plus12000_pass"],
                  "all_incremental_headroom_pass": result["all_six_incremental_headroom_pass"],
                  "all_outputs_match": result["all_six_outputs_match"],
                  "legacy_strict_b1_all": result["legacy_strict_b1_all_six_pass"],
                  "artifact": result["candidate_artifact_sha256"]}), flush=True)
