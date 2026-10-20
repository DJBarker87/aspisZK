#!/usr/bin/env python3
"""Fetch text receipts in one streamed archive; no archive/binary is retained."""
import shutil,subprocess,tarfile
from pathlib import Path
D=Path(__file__).resolve().parent
H='dombarker@100.108.41.90'
code="\nimport hashlib,json\nfrom pathlib import Path\nR=Path('/home/dombarker/project-offloads/codex-cx-prover-commit2-20261020')\nT=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence')\ndef pin(p):\n h=hashlib.sha256()\n with p.open('rb') as f:\n  for b in iter(lambda:f.read(1048576),b''):h.update(b)\n return dict(path=str(p),sha256=h.hexdigest(),bytes=p.stat().st_size)\nfiles=[]\nfor p in sorted((R/'receipts').rglob('*')):\n if p.is_file() and p.suffix in ['.json','.log']:files.append((str(p),str(p.relative_to(R/'receipts'))))\nfor a in range(8100,8400):\n m=R/('lean-'+str(a)+'.json')\n if not m.exists():continue\n files.append((str(m),'lean/'+str(a)+'/meta.json'))\n for remote,local in [('out','out'),('time','time')]:\n  p=T/(remote+'-'+str(a)+'.log')\n  if p.exists():files.append((str(p),'lean/'+str(a)+'/'+local+'.log'))\nfor pattern in ['*-source-pins.json','*-reservation.json','*cap-reduced.txt','*high-adjusted.txt']:\n for p in R.glob(pattern):files.append((str(p),p.name))\nfor name in ['source-pins.json','byte-identity.json','streams-byte-identity.json','retry.json','streams-retry.json','sim.json']:\n p=R/name\n if p.exists():files.append((str(p),name))\nllbc=[]\nfor p in sorted((R/'extraction').glob('*.llbc')):\n row=pin(p);d=json.loads(p.read_text());row.update(has_errors=d['has_errors'],charon_version=d['charon_version']);llbc.append(row)\nobjects=[]\nJ=Path('/home/dombarker/project-offloads/aspis-joint-20261019')\nfor prefix in ['AspisR1ProverCommit','AspisR1ProverStreams','AspisR1ProverLeaf','R1Z']:\n for p in sorted((J/'objects'/prefix).glob('*.olean')):\n  if prefix!='R1Z' or p.name.startswith('ProverCommit'):objects.append(pin(p))\n\nimport io,sys,tarfile\nfiles.append(('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json','env-J.json'))\nfiles.append((str(R/'source-kani/crates/aspis-prover/src/prover_commit_reference.rs'),'reference/prover_commit_reference.rs'))\nfiles.append((str(R/'library-model-check/Cargo.lock'),'library-model-check/Cargo.lock'))\ntools=[]\nfor name in ['/home/dombarker/.cargo/bin/cargo-kani','/home/dombarker/.kani/kani-0.67.0/bin/kani-compiler','/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/tools/run-joint.sh']:\n p=Path(name)\n if p.is_file():tools.append(pin(p))\nartifacts=dict(llbc=llbc,objects=objects,tools=tools)\nwith tarfile.open(fileobj=sys.stdout.buffer,mode='w|gz') as archive:\n for src,rel in files:archive.add(src,arcname=rel,recursive=False)\n data=(json.dumps(artifacts,indent=2)+'\\n').encode()\n info=tarfile.TarInfo('host-artifact-pins.json');info.size=len(data)\n archive.addfile(info,io.BytesIO(data))\n"
proc=subprocess.Popen(['ssh',H,'python3 -'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
proc.stdin.write(code.encode());proc.stdin.close()
count=0
with tarfile.open(fileobj=proc.stdout,mode='r|gz') as archive:
 for member in archive:
  assert member.isfile(),member.name
  target=(D/member.name).resolve()
  assert D in target.parents,member.name
  target.parent.mkdir(parents=True,exist_ok=True)
  with archive.extractfile(member) as source,target.open('wb') as output:shutil.copyfileobj(source,output)
  count+=1
assert proc.wait()==0
print(f'Fetched {count} text files; archives and binaries were not retained.')
