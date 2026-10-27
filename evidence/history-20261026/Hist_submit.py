import json, pathlib, subprocess, sys
n=int(sys.argv[1]);module=sys.argv[2];root=pathlib.Path(__file__).resolve().parent; tag=f"Hist_{n:03}"
c=json.loads((root/"Hist_082.json").read_text());c.update(attempt=tag,source_revision=subprocess.check_output(["git","rev-parse","HEAD"],text=True).strip(),sources=[module+".lean"],expected_time="Focused source provenance or association lemma; predecessor objects reused",source_tree_dirty=True)
c["command"][-3:]=["-o",module+".olean",module+".lean"]
p=root/(tag+".json");p.write_text(json.dumps(c,indent=2)+"\n")
h="dombarker@100.108.41.90";w="/home/dombarker/project-offloads/codex-cx-sound-int2-20261025"
subprocess.run(["scp","lean/"+module+".lean",str(p),h+":"+w+"/"],check=True)
r=subprocess.run(["ssh",h,f"cd {w} && systemd-run --user --scope --unit={tag} -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_lean_host.py {tag}.json"])
sys.exit(r.returncode)
