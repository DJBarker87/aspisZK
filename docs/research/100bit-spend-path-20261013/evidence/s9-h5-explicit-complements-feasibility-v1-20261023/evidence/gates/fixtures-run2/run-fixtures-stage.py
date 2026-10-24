from pathlib import Path
import hashlib, json, os, re, shutil, subprocess, sys, time

W=Path(__file__).resolve().parent
RUN=Path("/home/dombarker/project-offloads/a3-h5-explicit-complements-v1-20261023")
G=1024**3
CG=Path("/sys/fs/cgroup")/Path("/proc/self/cgroup").read_text().strip().removeprefix("0::").lstrip("/")
limits={k:(CG/k).read_text().strip() for k in ("memory.high","memory.max","memory.swap.max")}
assert limits=={"memory.high":str(G//4),"memory.max":str(G//2),"memory.swap.max":"0"},limits
src=RUN/"work/src"
artifact=RUN/"artifacts/aspis_r1_cost_probe_program.so"
assert artifact.is_file()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
build=json.loads((RUN/"gates/sbf/receipt.json").read_text())
assert sha(artifact)==build["candidate_artifact_sha256"]
manifest=src/"s9-candidate-source-manifest.json"
doc=json.loads(manifest.read_text())
actual={rel:sha(src/rel) for rel in doc["files"]}
assert actual==doc["files"], "candidate source changed after native/SBF receipt"
assert sha(W/"baseline-runs.json")=="a1b0a795f5101751950e42c7db19a1decfa3bd7f61d8ef37c85b211fa11a749f"
assert sha(W/"baseline-cu.json")=="a86721fad52e8b16fe3b1e8f6061ac2b1a6923ec730d7f24d50c601d294a473d"
assert sha(W/"verifier-strict-stack.py")=="eb8c6faaf1291eb2dbd66560bfe3f07b6f6734572b23875b79872b496e829287"
cases=[x for x in json.loads((W/"baseline-runs.json").read_text()) if x["name"].startswith("cu-")]
b1_rows=json.loads((W/"baseline-cu.json").read_text())
b1={x["fixture"]:x for x in b1_rows}
assert len(cases)==6 and len(b1)==6
E=RUN/"gates/fixtures"
E.mkdir(parents=True,exist_ok=False)
rows=[]
env=dict(os.environ);env["PATH"]="/home/dombarker/.cargo/bin:/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin:/usr/bin:/bin"
for case in cases:
 name=case["name"]
 cmd=case["command"].copy()
 baseline=json.loads(Path(cmd[4]).read_text())
 out=RUN/"runs"/name
 out.mkdir(parents=True,exist_ok=False)
 cmd[0]="/home/dombarker/project-offloads/codex-r1-format-adopt-20261019/artifacts/pool_gate_adopt"
 cmd[2]=str(artifact)
 cmd[4]=str(out/"evidence.json")
 cmd[5]=str(out/"task")
 input_hashes={"pool_so":sha(Path(cmd[1])),"candidate_so":sha(Path(cmd[2])),
               "registry_so":sha(Path(cmd[3])),"proof":sha(Path(cmd[11])),
               "public_asf":sha(Path(cmd[12]))}
 folder=E/name
 folder.mkdir(parents=True,exist_ok=False)
 (folder/"command.json").write_text(json.dumps({"argv":cmd,"cwd":"/home/dombarker/project-offloads/codex-cx-pin-20261020","candidate_artifact_sha256":sha(artifact),"source_manifest_sha256":sha(manifest),"baseline_runs_sha256":sha(W/"baseline-runs.json"),"b1_sha256":sha(W/"baseline-cu.json"),"input_artifact_and_proof_sha256":input_hashes,"timeout_seconds":60},indent=2)+"\n")
 before=(CG/"memory.events").read_text();start=time.monotonic();timed_out=False
 with (folder/"output.log").open("x") as log:
  try:
   result=subprocess.run(["/usr/bin/time","-v","-o",str(folder/"time.log"),*cmd],cwd="/home/dombarker/project-offloads/codex-cx-pin-20261020",env=env,stdout=log,stderr=subprocess.STDOUT,timeout=60)
   status=result.returncode
  except subprocess.TimeoutExpired:
   status=124;timed_out=True
 timing=(folder/"time.log").read_text() if (folder/"time.log").exists() else ""
 rss=re.search(r"Maximum resident set size \(kbytes\):\s*(\d+)",timing)
 receipt={"name":name,"exit_status":status,"timed_out":timed_out,"wall_seconds":round(time.monotonic()-start,3),
          "peak_process_rss_kib":int(rss[1]) if rss else None,"scope_peak_bytes":int((CG/"memory.peak").read_text()),
          "swap_current_bytes":int((CG/"memory.swap.current").read_text()),"memory_events_before":before,
          "memory_events_after":(CG/"memory.events").read_text(),"limits":limits,"candidate_artifact_sha256":sha(artifact)}
 (folder/"receipt.json").write_text(json.dumps(receipt,indent=2)+"\n")
 if status!=0: raise SystemExit(f"fixture command failed: {name}, exit {status}")
 data=json.loads((out/"evidence.json").read_text());actual_exec=data["execution"];expected=baseline["execution"]
 fixture=name.removeprefix("cu-"); old_b1=b1[fixture]
 stage1=actual_exec.get("stage1_compute_units");settlement=actual_exec.get("compute_units")
 stage1_base=expected["stage1_compute_units"];settlement_base=expected["compute_units"]
 row={"fixture":fixture,"candidate_artifact_sha256":sha(artifact),"input_artifact_and_proof_sha256":input_hashes,
      "candidate_evidence_sha256":sha(out/"evidence.json"),
      "stage1_cu":stage1,"stage1_baseline_cu":stage1_base,"stage1_delta_cu":stage1-stage1_base if stage1 is not None else None,
      "stage1_plus12214_limit_cu":stage1_base+12214,"stage1_plus12214_pass":stage1 is not None and stage1<=stage1_base+12214,
      "settlement_cu":settlement,"settlement_baseline_cu":settlement_base,"settlement_delta_cu":settlement-settlement_base if settlement is not None else None,
      "settlement_plus12214_limit_cu":settlement_base+12214,"settlement_plus12214_pass":settlement is not None and settlement<=settlement_base+12214,
      "legacy_b1_stage1_cu":old_b1["b1_stage1"],"legacy_b1_settlement_cu":old_b1["b1_settlement"],
      "legacy_b1_stage1_pass":stage1 is not None and stage1<=old_b1["b1_stage1"],
      "legacy_b1_settlement_pass":settlement is not None and settlement<=old_b1["b1_settlement"],
      "legacy_prior_runner_stage1_pass":stage1 is not None and stage1<=old_b1["b1_stage1"],
      "legacy_prior_runner_settlement_plus10000_pass":settlement is not None and settlement<=old_b1["b1_settlement"]+10000,
      "stage1_checkpoint_tail_same":actual_exec.get("stage1_checkpoint_tail_sha256")==expected["stage1_checkpoint_tail_sha256"],
      "return_data_same":actual_exec.get("return_data_sha256")==expected["return_data_sha256"],
      "run_receipt":receipt}
 row["approved_plus12214_pass"]=row["stage1_plus12214_pass"] and row["settlement_plus12214_pass"]
 row["legacy_strict_b1_pass"]=row["legacy_b1_stage1_pass"] and row["legacy_b1_settlement_pass"]
 rows.append(row)
 print(json.dumps({"fixture":fixture,"stage1":stage1,"stage1_delta":row["stage1_delta_cu"],"settlement":settlement,"settlement_delta":row["settlement_delta_cu"],"plus12214_pass":row["approved_plus12214_pass"],"legacy_strict_b1_pass":row["legacy_strict_b1_pass"]}),flush=True)
stack=RUN/"gates/fixtures-stack-input"
stack.mkdir(exist_ok=False)
linked=Path("/home/dombarker/project-offloads/s4-three-source-review-20261022/run1/work/sbf-target-verifier/sbpf-solana-solana/release/aspis_r1_cost_probe_program.so")
assert linked.is_file() and linked.stat().st_mtime >= (RUN/"gates/sbf/receipt.json").stat().st_mtime-2, "linked ELF predates this SBF phase"
shutil.copy(linked,stack/"linked.elf")
shutil.copy(artifact,stack/"stripped.so")
shutil.copy(RUN/"gates/sbf/stdout-stderr.log",stack/"build.log")
strict=W/"verifier-strict-stack.py"
stack_cmd=["python3",str(strict),str(stack)]
stack_folder=E/"strict-stack";stack_folder.mkdir(exist_ok=False)
with (stack_folder/"output.log").open("x") as log:
 before=(CG/"memory.events").read_text();start=time.monotonic()
 result=subprocess.run(["/usr/bin/time","-v","-o",str(stack_folder/"time.log"),*stack_cmd],cwd=W,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=60)
 timing=(stack_folder/"time.log").read_text();rss=re.search(r"Maximum resident set size \(kbytes\):\s*(\d+)",timing)
 stack_receipt={"argv":stack_cmd,"exit_status":result.returncode,"wall_seconds":round(time.monotonic()-start,3),
                "peak_process_rss_kib":int(rss[1]) if rss else None,"scope_peak_bytes":int((CG/"memory.peak").read_text()),
                "swap_current_bytes":int((CG/"memory.swap.current").read_text()),"memory_events_before":before,
                "memory_events_after":(CG/"memory.events").read_text(),"limits":limits,
                "candidate_artifact_sha256":sha(artifact),"linked_elf_sha256":sha(stack/"linked.elf"),
                "stripped_so_sha256":sha(stack/"stripped.so"),"build_log_sha256":sha(stack/"build.log")}
 (stack_folder/"receipt.json").write_text(json.dumps(stack_receipt,indent=2)+"\n")
 if result.returncode: raise SystemExit(f"strict stack check failed: {result.returncode}")
approved=all(r["approved_plus12214_pass"] for r in rows)
outputs_match=all(r["stage1_checkpoint_tail_same"] and r["return_data_same"] for r in rows)
result={"classification":"isolated S9 explicit-helper source candidate; no adoption/deployment",
        "research_head":doc["research_head"],"candidate_weights_sha256":doc["candidate_weights_sha256"],
        "source_manifest_sha256":sha(manifest),"candidate_artifact_sha256":sha(artifact),
        "six_fixture_rows":rows,"all_six_approved_plus12214_pass":approved,"all_six_outputs_match":outputs_match,
        "legacy_strict_b1_all_six_pass":all(r["legacy_strict_b1_pass"] for r in rows),
        "legacy_prior_runner_all_six_pass":all(r["legacy_b1_stage1_pass"] and r["legacy_prior_runner_settlement_plus10000_pass"] for r in rows),
        "strict_stack_receipt":stack_receipt,"limits":limits}
(RUN/"gates/gate-result.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps({"six_fixtures":len(rows),"all_plus12214_pass":approved,"all_outputs_match":outputs_match,"legacy_strict_b1_all":result["legacy_strict_b1_all_six_pass"],"artifact":result["candidate_artifact_sha256"]}),flush=True)
