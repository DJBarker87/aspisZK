"""Fixed immutable Git receipt examination; never imports or runs project code."""
import hashlib
import json
import pathlib
import resource
import subprocess
import sys
import time

START = time.monotonic()
REV = "eccc7281331722dca97dfaf7cd605478169abacf"
OUT = pathlib.Path(__file__).resolve().parent
INPUTS = {}

def git(*args):
    return subprocess.check_output(["git", *args], timeout=5)

def blob(path, rev=REV, limit=1024 * 1024):
    data = git("show", rev + ":" + path)
    assert len(data) < limit, (path, len(data))
    INPUTS[rev + ":" + path] = dict(bytes=len(data), sha256=hashlib.sha256(data).hexdigest())
    return data

def parsed(path):
    return json.loads(blob(path))

jobs = ["port7clean", "port13gate", "port15driver", "port16cut", "port17release",
        "port18coherence", "port18validate", "port18final", "port19rest", "port20alloc",
        "port21projection", "port22arena", "port23push", "port24sbfmap", "port25array",
        "port26row", "port27sdk", "port28rootexport"]
roots = ["evidence/" + j + "-20261024" for j in jobs]
paths = git("ls-tree", "-r", "--name-only", REV, "--", *roots).decode().splitlines()
receipts = [p for p in paths if p.endswith("/receipt.json") and "/lean-" in p]
assert len(receipts) < 200
inventory = []
for p in receipts:
    d = parsed(p)
    command = d.get("command", [])
    linux = str(command).find("/home/dombarker/") >= 0
    inventory.append(dict(path=p, command=command, exit=d.get("exit_status"),
                          source_revision=d.get("source_revision"), linux_path=linux,
                          wall_seconds=d.get("wall_seconds")))

selected = {}
for job, n in [("port7clean", 27), ("port13gate", 5), ("port15driver", 19),
               ("port16cut", 10), ("port17release", 13), ("port17release", 24),
               ("port17release", 25), ("port18coherence", 11)]:
    base = f"evidence/{job}-20261024/lean-{n:03}"
    d = parsed(base + "/receipt.json")
    for name, sha in d["source_hashes"].items():
        assert hashlib.sha256(blob(base + "/sources/" + name)).hexdigest() == sha
    # RootSnapshot's released textual diagnostic is 4,867,752 bytes.
    stdout = blob(base + "/stdout.log", limit=5 * 1024 * 1024).decode()
    assert all(line in stdout for line in d.get("print_axioms", []))
    blob(base + "/time.log")
    stamps = []
    for suffix in ["-reservation.json", "-before.json", "-go.json"]:
        path = base + suffix
        if path in paths:
            a = parsed(path)
            stamps.append(dict(path=path, **{k:v for k,v in a.items()
                          if not isinstance(v, (dict, list))}))
    selected[base] = dict(receipt=d, admission=stamps,
        receipt_commit=git("log", "-1", "--format=%H %aI %cI %s", REV, "--", base + "/receipt.json").decode().strip())

for job, prefix in [("port7clean", "Port7CLEAN"), ("port17release", "Port17RELEASE"),
                    ("port18coherence", "Port18COHERENCE")]:
    for suffix in ["compile", "run_host", "admission"]:
        if job == "port7clean" and suffix == "admission":
            continue  # This historical job used an inherited admission helper.
        path = f"tools/{job}-20261024/{prefix}_{suffix}.py"
        blob(path)
for suffix in ["lean_host"]:
    blob(f"tools/port17release-20261024/Port17RELEASE_{suffix}.py")

reviews = ["port36-364-v1", "port36-365-v1", "port36-366-v1", "port36-linux-source-v1",
           "final-native-data-action-v1", "final-native-data-v4-action-v1",
           "final-native-receipt-action-v1", "final-native-admission-action-v1",
           "final-native-v5-action-v1", "a-claims-ranges-v1"]
for name in reviews:
    parsed("evidence/lead-review-20261025/" + name + ".json")
blob("tools/port36transport-20261025/linux367/Port36LINUX_caller.py", "c0da01870c")
hist = "docs/research/v8-r0-zk-20261009/t2b2b/build-integration/"
for name in ["run-joint.sh.txt", "joint-drive.py.txt", "joint-drive-range.py.txt",
             "manifest-2-completion-20261019.json", "joint-attempts-5532-5547.jsonl"]:
    blob(hist + name)
historical_5547 = json.loads(blob(hist + "joint-attempts-5532-5547.jsonl").splitlines()[-1])
for name in ["observation-summary.json", "capture-stdout.json"]:
    parsed("evidence/lean-host-probe-20261025/action-afterleadreview-v1/" + name)

out = dict(examined_revision=REV, scope="Fixed released root receipt families; not all branches/global latest",
           inventory=inventory, selected=selected, historical_5547=historical_5547, inputs=INPUTS,
           claims="Historical execution provenance only; no theorem/premise/release/security change",
           new_host_compiler_lean_kani_calls=0, print_axioms="N/A forensic data review")
(OUT / "receipts.json").write_text(json.dumps(out, indent=2) + "\n")
u = resource.getrusage(resource.RUSAGE_SELF)
c = resource.getrusage(resource.RUSAGE_CHILDREN)
scale = 1 if sys.platform == "darwin" else 1024
assert max(u.ru_maxrss, c.ru_maxrss) * scale < 512 * 2**20
assert time.monotonic() - START < 30
check = dict(command=["python3", "-B", "evidence/launch-history-20261025/collect.py"],
    target="fixed immutable launcher receipt and source-hash checks", exit=0,
    wall_seconds=time.monotonic()-START, self_peak_rss_bytes=u.ru_maxrss*scale,
    max_serial_child_rss_bytes=c.ru_maxrss*scale, aggregate_peak="UNOBSERVED",
    self_swap_counter=u.ru_nswap, child_swap_counter=c.ru_nswap,
    source_revision=git("rev-parse", "HEAD").decode().strip(),
    collector_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
    dependencies="Python standard library + read-only git show/ls-tree/log; exact input hashes in receipts.json",
    print_axioms="N/A: no Lean or theorem validation", receipt_count=len(inventory),
    input_count=len(INPUTS), new_host_compiler_lean_kani_calls=0)
(OUT / "validation.json").write_text(json.dumps(check, indent=2) + "\n")
print(json.dumps(check))
