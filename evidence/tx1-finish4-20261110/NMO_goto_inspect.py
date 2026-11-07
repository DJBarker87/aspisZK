from pathlib import Path
import subprocess,json,hashlib,lzma
B=Path.cwd();T=B/'NMO_target/kani/x86_64-unknown-linux-gnu/debug/deps'
found=[]
for p in T.glob('aspis_r1_cost_probe-*.kani-metadata.json'):
 for h in json.loads(p.read_text()).get('proof_harnesses',[]):
  if h.get('pretty_name')=='r1_semantic::NMO_terminal::NMO_terminal_error':found.append((p,h))
assert len(found)==1
p,h=found[0];model=Path(h['goto_file']).with_name(Path(h['goto_file']).name.replace('.symtab.out','.out'))
cmd=['/home/dombarker/.kani/kani-0.67.0/bin/goto-instrument','--reachable-call-graph',str(model)]
r=subprocess.run(cmd,capture_output=True);assert r.returncode==0,r.stderr.decode()
raw=r.stdout;(B/'NMO_TERMINAL_CALLGRAPH.txt.xz').write_bytes(lzma.compress(raw));(B/'NMO_TERMINAL_CALLGRAPH.txt.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
text=raw.decode();out=dict(command=cmd,exit=r.returncode,metadata_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),model_sha256=hashlib.sha256(model.read_bytes()).hexdigest(),harness=h,callgraph_bytes=len(raw),lines=len(text.splitlines()),callgraph_sha256=hashlib.sha256(raw).hexdigest(),field_mentions=[l for l in text.splitlines()if 'field' in l and ('mul' in l or 'add' in l)])
(B/'NMO_GOTO_INSPECTION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k]for k in ['exit','callgraph_bytes','lines','field_mentions']}))
