from pathlib import Path
import tarfile,hashlib,json,io
b=Path("/home/dombarker/project-offloads/aspis-r1-j1a-terminal-decoder-20261016")
sha=lambda d:hashlib.sha256(d).hexdigest()
files={}
for sub in ["", "before", "indexed", "status"]:
 w=b/sub
 for rel in ["run-host.py","input/source-pins.json","native-artifact.json","extraction-a/TerminalDecoder.llbc"]:
  p=w/rel
  if p.is_file():files[str(p.relative_to(b))]=p.read_bytes()
 for p in sorted((w/"runs").rglob("*")):
  if p.is_file():files[str(p.relative_to(b))]=p.read_bytes()
 pins=json.loads((w/"input/source-pins.json").read_text())
 for rel in pins["kit_files"]:
  p=w/"input"/rel
  if sha(p.read_bytes())!=pins["kit_files"][rel]:raise ValueError(str(p))
 for rel in ["crates/aspis-statement/src/atomic_statement.rs","crates/aspis-statement/src/pool_v1/pair_tree_profile.rs","crates/aspis-statement/src/pool_v1/pair_terminal.rs","crates/aspis-statement/examples/j1_terminal_decoder_trace.rs"]:
  p=w/"input"/rel
  if p.is_file():files[str(p.relative_to(b))]=p.read_bytes()
files["collect-failures.py"]=Path(__file__).read_bytes()
manifest={n:{"bytes":len(d),"sha256":sha(d)} for n,d in files.items()}
files["archive-members.json"]=(json.dumps(manifest,indent=2,sort_keys=True)+"\n").encode()
p=b/"failed-extraction-evidence.tar.gz"
with tarfile.open(p,"w:gz") as t:
 for n,d in sorted(files.items()):
  info=tarfile.TarInfo(n);info.size=len(d);info.mode=0o644;t.addfile(info,io.BytesIO(d))
print(json.dumps({"archive":str(p),"sha256":sha(p.read_bytes()),"bytes":p.stat().st_size,"members":len(files)},sort_keys=True))
