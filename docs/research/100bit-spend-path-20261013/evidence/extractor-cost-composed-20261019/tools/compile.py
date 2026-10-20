#!/usr/bin/env python3
"""Sequential focused Lean replay with the shared macOS mkdir lock."""
import hashlib, json, os, pathlib, re, subprocess, sys, time
root = pathlib.Path(__file__).resolve().parents[6]
packet = pathlib.Path(__file__).resolve().parents[1]
module = sys.argv[1]
config = json.loads(subprocess.check_output(["git", "show", "d1281b25f:docs/research/100bit-spend-path-20261013/evidence/extractor-cost-composed-20261019/RawExtractorCostLedger/command.json"], cwd=root, text=True))
objects = pathlib.Path("/tmp/cx-m10-extractor-cost-resume-20261020-objects")
objects.mkdir(exist_ok=True)
supplement = json.loads((packet.parent / "checked-acceptance-no-clean-model-premise-20261019/RawChecksAdaptiveFailureNoModel/command.json").read_text())["lean_path"]
lean_path = ":".join(dict.fromkeys(([str(objects)] + config["lean_path"].split(":") + supplement.split(":"))))
source = root / "docs/research/100bit-spend-path-20261013/lean" / (module + ".lean")
lock = pathlib.Path("/tmp/aspis-local-lean.lock.d")
def running():
    ps = subprocess.check_output(["ps", "-axo", "pid=,comm=,args="], text=True)
    return [l for l in ps.splitlines() if re.search(r"/bin/lean\s", l) and "-M4400" in l]
while True:
    try:
        lock.mkdir()
    except FileExistsError:
        if time.time()-lock.stat().st_mtime > 1800 and not running():
            try: lock.rmdir()
            except OSError: pass
        time.sleep(15)
        continue
    if running():
        lock.rmdir()
        time.sleep(60)
        continue
    break
out = packet / module
out.mkdir(exist_ok=True)
cmd = ["/usr/bin/time", "-l", "/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean", "-j1", "-M4400", "-DElab.async=false", "-o", str(objects/(module+".olean")), str(source)]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
command = dict(module=module,cwd=str(root),command=cmd,lean_path=lean_path,source_revision=revision,source_sha256=sha(source),executed=True,lock=str(lock))
(out/"command.json").write_text(json.dumps(command,indent=2)+"\n")
try:
    start=time.monotonic()
    with (out/"stdout.txt").open("w") as stdout, (out/"stderr.txt").open("w") as stderr:
        process=subprocess.run(cmd,cwd=root,env={**os.environ,"LEAN_PATH":lean_path},stdout=stdout,stderr=stderr)
    elapsed=time.monotonic()-start
finally:
    lock.rmdir()
stderr=(out/"stderr.txt").read_text()
stdout=(out/"stdout.txt").read_text()
def metric(label):
    m=re.search(r"(\d+)\s+"+label,stderr)
    return int(m[1]) if m else None
receipt=dict(command,exit_status=process.returncode,wall_seconds=elapsed,peak_rss_bytes=metric("maximum resident set size"),process_swap_count=metric("swaps"),swap_bytes=None,swap_note="time -l reports swap count; per-process swap bytes unavailable",axioms_result=stdout,object_sha256=sha(objects/(module+".olean")) if process.returncode==0 else None)
(out/"receipt.json").write_text(json.dumps(receipt,indent=2)+"\n")
print(json.dumps({k:receipt[k] for k in ["module","exit_status","wall_seconds","peak_rss_bytes","process_swap_count"]}))
print(stdout)
sys.exit(process.returncode)
