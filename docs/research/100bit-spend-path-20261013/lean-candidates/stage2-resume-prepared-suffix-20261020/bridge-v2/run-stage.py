#!/usr/bin/env python3
"""Focused coherent suffix-owner rebuild and prefix/suffix alpha bridge."""
from pathlib import Path
import hashlib, json, os, re, subprocess, time

W = Path(__file__).resolve().parent
C = json.loads((W / "config.json").read_text())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
cgline = Path("/proc/self/cgroup").read_text().strip()
assert cgline.startswith("0::")
cg = Path("/sys/fs/cgroup") / cgline[3:].lstrip("/")
limits = {n: (cg / n).read_text().strip() for n in
          ["memory.high", "memory.max", "memory.swap.max"]}
assert limits == {"memory.high": str(512*2**20),
                  "memory.max": str(2*2**30), "memory.swap.max": "0"}, limits

def first_hit(rel):
    hits = [Path(r) / rel for r in C["lean_path"] if (Path(r) / rel).is_file()]
    assert hits, rel
    return hits[0], sha(hits[0])

selected = {}
for rel, wanted in C["expected_imports"].items():
    path, got = first_hit(rel)
    assert got == wanted, (rel, str(path), got, wanted)
    selected[rel] = {"path": str(path), "sha256": got}

out = W / "runs" / "bridge-v2"
out.mkdir(parents=True, exist_ok=False)
obj = W / "attempt" / "objects"
obj.mkdir(parents=True, exist_ok=True)
lean = C["lean"]
env = dict(os.environ)
env["LEAN_PATH"] = ":".join([str(obj), *C["lean_path"]])
sources = [
    (W / "generated/AspisR1Stage2ResumeSuffix/Types.lean", obj / "AspisR1Stage2ResumeSuffix/Types.olean"),
    (W / "generated/AspisR1Stage2ResumeSuffix/Funs.lean", obj / "AspisR1Stage2ResumeSuffix/Funs.olean"),
    (W / "proofs/SuffixPreparedFields.lean", obj / "SuffixPreparedFields.olean"),
    (W / "proofs/PrefixSuffixAlphaBridge.lean", obj / "PrefixSuffixAlphaBridge.olean"),
]
for source, _ in sources:
    assert sha(source) == C["source_hashes"][str(source.relative_to(W))]
before = (cg / "memory.events").read_text()
start = time.monotonic(); sampled = 0; records=[]
for idx, (source, dest) in enumerate(sources):
    dest.parent.mkdir(parents=True, exist_ok=True)
    cmd = [lean, "-M4400", "-j1", "-R", str(W / ("generated" if "generated" in str(source) else "proofs")), "-o", str(dest), str(source)]
    timing=out/f"{idx}.time.log"; log=out/f"{idx}.lean.log"; begin=time.monotonic()
    with log.open("x") as lf:
        p=subprocess.Popen(["/usr/bin/time","-v","-o",str(timing),*cmd],cwd=source.parent,env=env,stdout=lf,stderr=subprocess.STDOUT,start_new_session=True)
        while p.poll() is None:
            sampled=max(sampled,int((cg/"memory.current").read_text()))
            if time.monotonic()-begin>120:
                p.terminate();p.wait();break
            time.sleep(.2)
        p.wait()
    t=timing.read_text() if timing.exists() else ""
    def num(label):
        m=re.search(re.escape(label)+r":\s*(\d+)",t);return int(m[1]) if m else None
    rec={"source":str(source.relative_to(W)),"source_sha256":sha(source),"command":cmd,"exit_status":p.returncode,"wall_seconds":time.monotonic()-begin,"peak_process_rss_kib":num("Maximum resident set size (kbytes)"),"process_swaps":num("Swaps"),"log":str(log.relative_to(W)),"time_log":str(timing.relative_to(W))}
    if p.returncode==0: rec["object_sha256"]=sha(dest)
    records.append(rec)
    if p.returncode: break
receipt={"phase":"bridge-v2","exit_status":records[-1]["exit_status"],"wall_seconds":time.monotonic()-start,"peak_process_rss_kib":max(r["peak_process_rss_kib"] or 0 for r in records),"process_swaps":sum(r["process_swaps"] or 0 for r in records),"sampled_cgroup_peak_bytes":sampled,"cgroup_peak_bytes":int((cg/"memory.peak").read_text()),"cgroup_swap_current":int((cg/"memory.swap.current").read_text()),"memory_events_before":before,"memory_events_after":(cg/"memory.events").read_text(),"limits":limits,"commands":records,"lean_path":env["LEAN_PATH"],"selected_imports":selected,"source_hashes":C["source_hashes"],"source_pins_sha256":sha(W/"source-pins.json"),"scope":"Private suffix Error discriminant-attribute removal prevents the generated global instance collision; prefix reader and suffix constructor successes remain separate hypotheses.","classification":"Candidate bridge only; no full resume reachability claim; only the Error discriminant attribute is removed in the private suffix Types copy."}
(out/"receipt.json").write_text(json.dumps(receipt,indent=2)+"\n")
print(json.dumps(receipt),flush=True)
raise SystemExit(receipt["exit_status"])
