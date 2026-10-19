from pathlib import Path
import re,json,hashlib
w=Path("/home/dombarker/project-offloads/aspis-r1-recut-sbf-20261018");syms=w/"stack-supplemental/symbols.txt";dis=w/"stack-supplemental/disassembly.txt";functions={}
for line in syms.read_text().splitlines():
 m=re.match(r"\s*\d+: ([0-9a-f]+)\s+(\d+) FUNC\s+\S+\s+\S+\s+(\d+) (\S+)",line)
 if m:functions[m[4]]={"address":int(m[1],16),"size":int(m[2])}
addresses={v["address"]:k for k,v in functions.items()};tx1=next(k for k in functions if "verifier3tx117h" in k);current=None;calls=[]
for line in dis.read_text().splitlines():
 m=re.match(r"[0-9a-f]+ <([^>]+)>:",line)
 if m:current=m[1]
 if current!=tx1:continue
 m=re.match(r"\s*([0-9a-f]+):\s+call (0x[0-9a-f]+|-0x[0-9a-f]+)",line)
 if m:
  imm=int(m[2],16)
  if imm>=2**31:imm-=2**32
  addr=int(m[1],16)+8+8*imm;calls.append({"instruction":line.strip(),"target_address":addr,"target_symbol":addresses.get(addr)})
 if re.search(r"\bcallx\b",line):calls.append({"instruction":line.strip(),"indirect":True})
result={"revision":"234a1431ba0ec533261864b6d34c86997c70239d","tx1_symbol":tx1,"tx1":functions[tx1],"finish_symbols":[k for k in functions if "tx1_finish" in k],"finish_disassembly_references":dis.read_text().count("tx1_finish"),"calls":calls,"conclusion":"No surviving separate tx1_finish function/call in complete current linked symbol/disassembly inventory; an inline attribute is not demonstrated to remove a current function-call boundary. No source change/rebuild performed.","inputs":{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [syms,dis,w/"sbf-target/sbpf-solana-solana/release/aspis_r1_cost_probe_program.so"]}}
(w/"tx1-call-inventory.json").write_text(json.dumps(result,indent=2)+"\n");print(json.dumps(result,indent=2))
