from pathlib import Path
import subprocess,json,hashlib
B=Path.cwd();p=B/'PCG_target/kani/x86_64-unknown-linux-gnu/debug/deps/aspis_pool.kani-metadata.json';m=json.loads(p.read_text());h=next(h for h in m['proof_harnesses'] if h['pretty_name']=='pair_forest::PCG_324::actual_call_structure');g=Path(h['goto_file']);tool=Path('/home/dombarker/.kani/kani-0.67.0/bin/goto-instrument')
cmd=[str(tool),'--function',h['mangled_name'],'--remove-unused-functions','--show-call-graph',str(g)]
r=subprocess.run(cmd,capture_output=True,text=True);(B/'PCG_K074_callgraph.txt').write_text(r.stdout+r.stderr);(B/'PCG_K074_GOTO.json').write_text(json.dumps(dict(harness=h,command=cmd,exit=r.returncode,binary_sha256=hashlib.sha256(g.read_bytes()).hexdigest(),tool_sha256=hashlib.sha256(tool.read_bytes()).hexdigest(),stdout_sha256=hashlib.sha256(r.stdout.encode()).hexdigest()),indent=1)+'\n');print('K074 callgraph inspection exit'+str(r.returncode));raise SystemExit(r.returncode)
