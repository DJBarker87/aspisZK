import hashlib,io,json,subprocess,tarfile
from pathlib import Path
root=Path.cwd(); out=root/'.j1-digest32-native';sha=lambda b:hashlib.sha256(b).hexdigest()
fixture='docs/research/100bit-spend-path-20261013/evidence/p3-private-leaf-salts-20261013/p3-pool-13/transfer-1023-os-task/'
paths=['Cargo.toml','Cargo.lock','crates','programs','xtask','audit/poseidon-pair-probe/program','tools/r1-hash-input-counter',fixture+'r1-s2-proof.bin',fixture+'r1-s2-public-asf8.bin','results/spend/v7-devnet-20260825-fullc2/v7-proof.bin']
for label,revision in [('after','HEAD'),('before','ca137f5db')]:
 rev=subprocess.check_output(['git','rev-parse',revision],text=True).strip()
 data=subprocess.check_output(['git','archive',rev,*paths]); files={}
 with tarfile.open(fileobj=io.BytesIO(data)) as tar:
  for member in tar.getmembers():
   if member.isfile(): files[member.name]=tar.extractfile(member).read()
 alterations={}
 if label=='before':
  p='tools/r1-hash-input-counter/src/main.rs'
  candidate=(root/p).read_text();begin=candidate.index('#[derive(Clone, Copy)]\nstruct CountedDigest;');end=candidate.index('static PHASE:',begin)
  modified=candidate[:begin]+candidate[end:];modified=modified.replace(', CountedDigest, None',', counted_hash, None')
  alterations[p]={'original_sha256':sha(files[p]),'candidate_source_sha256':sha(candidate.encode()),'instrumented_sha256':sha(modified.encode()),'rule':'Identical candidate counter instrumentation, remove only CountedDigest definition/impl and use the original counted_hash function at both verifier calls.'};files[p]=modified.encode()
 manifest={'source_revision':rev,'label':label,'files':{p:sha(b) for p,b in sorted(files.items())},'instrumentation_changes':alterations,'scope':'All workspace source plus exact selected include fixtures; no key material, proof generation or release ELF.'}
 dest=out/f'{label}.tar.gz'
 with tarfile.open(dest,'w:gz') as tar:
  for p,b in sorted(files.items()):
   m=tarfile.TarInfo(p);m.size=len(b);m.mode=0o644;tar.addfile(m,io.BytesIO(b))
 manifest['archive_sha256']=sha(dest.read_bytes());(out/f'{label}-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
 print(label,rev,len(files),dest.stat().st_size,manifest['archive_sha256'])
# Retained exact1233 stdout and producing evidence, without rebuilding baseline.
p=root/'docs/research/100bit-spend-path-20261013/evidence/terminal-validator-extraction-20261016/evidence.tar.gz'
with tarfile.open(p) as tar:
 names=['trace-comparison.json','helper/runs/trace-a/stdout.log','helper/runs/trace-a/receipt.json','helper/runs/trace-a/environment.json','helper/input/crates/aspis-statement/examples/j1_terminal_codec_trace.rs','helper/native-source-freshness.json','helper/native-artifact.json']
 for n in names:
  dest=out/'codec-baseline'/n;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(tar.extractfile(n).read())
 current=(root/'crates/aspis-statement/examples/j1_terminal_codec_trace.rs').read_bytes(); assert current==tar.extractfile(names[4]).read()
 (out/'codec-baseline/reuse.json').write_text(json.dumps({'archive_sha256':sha(p.read_bytes()),'trace_source_unchanged':True,'trace_source_sha256':sha(current),'retained_files':{n:sha(tar.extractfile(n).read()) for n in names}},indent=2)+'\n')
