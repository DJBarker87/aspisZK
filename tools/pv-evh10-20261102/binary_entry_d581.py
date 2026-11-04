"""Read-only adopted binary analysis payload; run in assigned capped native scope."""
from pathlib import Path
import subprocess, hashlib, json, re
p=Path('/home/dombarker/project-offloads/codex-pv-c474-20261029/native-target/client/devnet_spend')
raw=p.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='da36d6aa36f8566ffa2ce7276546941c745bcd6325613c5a98c5517328b7def0'
def run(*args): return subprocess.check_output(args,text=True)
asm=run('objdump','-d','-C',str(p))
functions=re.split(r'(?=^[0-9a-f]+ <[^\n]+>:$)',asm,flags=re.M)
selected=[]
for f in functions:
 header=f.splitlines()[0] if f else ''
 if any(t in header for t in ['prove_for_proof_accounts','prove_masked_retrying_with','prover::retry_attempt','StateOnlyAttemptSecrets::generate_for_mask_nonce','devnet_spend::main','as zeroize::Zeroize>::zeroize']):
  selected.append(dict(header=header,disassembly=f))
rel=run('readelf','-rW',str(p))
# All statically named call references to the selected entry/helper targets.
targets={int(re.match(r'([0-9a-f]+)',f['header'])[1],16) for f in selected if 'devnet_spend::main' not in f['header']}
got={int(l.split()[0],16):int(l.split()[-1],16) for l in rel.splitlines() if 'R_X86_64_RELATIVE' in l}
refs=[]
for f in functions:
 lines=f.splitlines();header=lines[0] if lines else ''
 for i,l in enumerate(lines):
  direct=re.search(r'\b(?:call|jmp)\s+([0-9a-f]+)\b',l)
  indirect=re.search(r'#\s+([0-9a-f]+)\b',l)
  if (direct and int(direct[1],16) in targets) or (indirect and got.get(int(indirect[1],16)) in targets):
   refs.append(dict(function=header,instruction=l,window='\n'.join(lines[max(0,i-18):i+6])))
tools={}
for name in ['objdump','nm','readelf']:
 path=run('which',name).strip();tools[name]=dict(path=path,sha256=hashlib.sha256(Path(path).read_bytes()).hexdigest(),version=run(name,'--version').splitlines()[0])
print(json.dumps(dict(binary=dict(path=str(p),sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw),executed=False),tools=tools,symbols=[l for l in run('nm','-n','-S','-C',str(p)).splitlines() if any(t in l for t in ['prove_for_proof_accounts','prove_masked_retrying_with','retry_attempt','generate_for_mask_nonce','devnet_spend::main'])],functions=selected,references=refs,relocations=[l for l in rel.splitlines() if 'R_X86_64_RELATIVE' in l and int(l.split()[-1],16) in targets],evidence_class='binary-structural (adopted binary), plus V370 compiler-cohort')))
