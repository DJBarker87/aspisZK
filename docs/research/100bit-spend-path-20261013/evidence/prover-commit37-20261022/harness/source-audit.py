#!/usr/bin/env python3
"""Read-only pins and selected native hash-frame inspection; no compilation."""
import hashlib,json,re,subprocess
from pathlib import Path
E=Path(__file__).resolve().parent.parent
base=(E/'pins/revision.txt').read_text().strip()
def sha(b): return hashlib.sha256(b).hexdigest()
def write(name,data): (E/name).write_text(json.dumps(data,indent=2)+'\n')
reservation=b'aspis:state-only:attempt-reservation:v1'
assert len(reservation)==39 and reservation[32]==116
files=[
 'crates/aspis-prover/src/state_only_entropy.rs',
 'crates/aspis-prover/src/state_only_hiding.rs',
 'crates/aspis-r1-cost-probe/src/prover.rs',
 'crates/aspis-r1-cost-probe/src/sim.rs',
 'crates/aspis-core/src/r0/transcript.rs',
 'crates/aspis-core/src/transcript.rs',
 'crates/aspis-core/src/r0/merkle.rs',
 'crates/aspis-core/src/merkle.rs',
 'crates/aspis-core/src/state_only_private_merkle.rs',
 'crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs',
]
pins=[];domains=[]
for f in files:
 b=Path(f).read_bytes();s=b.decode();pins.append(dict(path=f,sha256=sha(b),size=len(b)))
 for m in re.finditer(r'(?:pub )?const\s+([A-Z][A-Z0-9_]*DOMAIN)\s*:[^=]*=\s*b"([^"\\]*)";',s):
  name,domain=m[1],m[2].encode()
  if domain==reservation: continue
  k=min(len(domain),len(reservation))
  assert domain[:k]!=reservation[:k],(f,name)
  domains.append(dict(path=f,line=s[:m.start()].count('\n')+1,name=name,
    ascii=domain.decode(),prefixes_disjoint=True))
checks={
 'reservation_direct_sha256':('crates/aspis-prover/src/state_only_entropy.rs',[
  'hasher.update(ATTEMPT_RESERVATION_DOMAIN);','hasher.update(mask_nonce);']),
 'public_first_byte':('crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs',[
  'CompiledVariant::PrivateTransfer => 0,','CompiledVariant::Withdrawal => 1,']),
 'r0_state_absorb':('crates/aspis-core/src/r0/transcript.rs',[
  '&self.state, &[0, 0xa0 + row], &[tag], &len, payload','&s, &[1]','&s, &[2]']),
 'legacy_state_controls':('crates/aspis-core/src/transcript.rs',[
  'const DOM_ABSORB: u8 = 0x00;','const DOM_SQUEEZE: u8 = 0x01;',
  'const DOM_ADVANCE: u8 = 0x02;','const DOM_GRIND: u8 = 0x03;']),
 'r0_merkle':('crates/aspis-core/src/r0/merkle.rs',['&[0x10, tag]','&[0x18]']),
 'p3_binding':('crates/aspis-r1-cost-probe/src/prover.rs',['b"UNPROVED:R1:P3:PRIVATE-ATTEMPT"']),
 'sim_coin':('crates/aspis-r1-cost-probe/src/sim.rs',['b"UNPROVED:R1:SIM:COIN"']),
}
checked=[]
for name,(f,needles) in checks.items():
 s=Path(f).read_text()
 for needle in needles:
  assert needle in s,(name,needle)
  checked.append(dict(check=name,path=f,line=s[:s.index(needle)].count('\n')+1,source=needle))
write('source-frames.json',dict(source_revision=base,reservation_domain=reservation.decode(),
 input_length=71,first_byte=97,byte_at_32=116,source_pins=pins,
 constant_domains=domains,checked_source_fragments=checked,
 conclusion='Selected native protocol frame families are separated by first byte, fixed domain prefix, or byte 32. Adversarial oracle queries remain unrestricted.',
 limitation='Source inspection and grammar lemmas; not a verified complete source-to-ROM call-graph refinement.'))

paths=subprocess.check_output(['git','ls-files','-z','--','crates','programs']).split(b'\0')
rows=[]
for pb in paths:
 if not pb:continue
 f=pb.decode();current=Path(f).read_bytes()
 original=subprocess.check_output(['git','show',base+':'+f])
 assert current==original,f
 rows.append(dict(path=f,sha256=sha(current),size=len(current)))
assert not subprocess.check_output(['git','diff',base,'--','crates','programs']).strip()
write('shipped-sources-unchanged.json',dict(base=base,count=len(rows),all_byte_identical=True,files=rows))

endpoints=['ProverCommitDeployedFuel22','PrivacyR1HeadlineDeployed','ProverCommitTrustedStd24']
D=E/'endpoint';D.mkdir(exist_ok=True);ep=[]
for m in endpoints:
 f='docs/research/v8-r0-zk-20261009/lean/R1Z/'+m+'.lean'
 b=Path(f).read_bytes();old=subprocess.check_output(['git','show',base+':'+f]);assert b==old
 (D/(m+'.before.lean.txt')).write_bytes(old)
 (D/(m+'.after.lean.txt')).write_bytes(b)
 ep.append(dict(path=f,sha256=sha(b),size=len(b),unchanged=True))
(D/'diff.txt').write_text(subprocess.check_output(['git','diff',base,'--',*[r['path'] for r in ep]],text=True))
write('endpoint/unchanged.json',dict(base=base,files=ep))
print('Source frame pins, shipped source inventory and unchanged endpoints recorded.')
