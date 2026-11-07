"""Source-fission check and registry input pins. No source/tool mutation."""
from pathlib import Path
import json,hashlib,re,tomllib,tarfile
B=Path.cwd();S=B/'PCG_src';R=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f')
sha=lambda b:hashlib.sha256(b).hexdigest()
files={}
for package in ['solana-pubkey-2.4.0','solana-define-syscall-2.3.0']:
 root=R/package;name,version=package.rsplit('-',1)
 archive=R.parent.parent/'cache'/R.name/(package+'.crate')
 archive_sha=sha(archive.read_bytes());tar=tarfile.open(archive)
 lock=tomllib.loads((S/'Cargo.lock').read_text());entry=next(p for p in lock['package'] if p['name']==name and p['version']==version)
 assert entry['checksum']==archive_sha
 for n in ['Cargo.toml','Cargo.toml.orig','src/lib.rs','src/syscalls.rs','src/definitions.rs']:
  p=root/n
  if not p.exists():continue
  raw=p.read_bytes();assert raw==tar.extractfile(package+'/'+n).read(),str(p)
  target=B/'PCG_SDK_INPUTS'/package/n;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(raw)
  files[str(target.relative_to(B))]=dict(source=str(p),sha256=sha(raw),bytes=len(raw),package_checksum=archive_sha)
sdk=(R/'solana-pubkey-2.4.0/src/lib.rs').read_text()
start=sdk.index('    pub fn create_program_address(');end=sdk.index('    pub const fn to_bytes',start);create=sdk[start:end]
start=create.index('            let mut bytes = [0; 32];');end=create.index('\n        }',start)
original=create[start:end]
text=(S/'programs/aspis-pool/src/PCG_SdkPda.rs').read_text();start=text.index('    let mut bytes = [0; 32];',text.index('fn create_tail('));end=text.index('\n}',start);segment=text[start:end]
normalize=lambda s:re.sub(r'\s+','',s).replace('crate::syscalls::','solana_program::pubkey::syscalls::').replace('SUCCESS=>','0=>')
assert normalize(original)==normalize(segment),'SDK tail differs'
# Reject meaningful mutations; whitespace/alias resolution alone is permitted.
mutations={
 'wrong_count':segment.replace('seeds.len() as u64','0'),
 'wrong_program':segment.replace('program_id as *const _ as *const u8','seeds as *const _ as *const u8'),
 'wrong_seed_pointer':segment.replace('seeds as *const _ as *const u8','program_id as *const _ as *const u8',1),
 'wrong_result':segment.replace('Ok(Pubkey::from(bytes))','Err(PubkeyError::InvalidSeeds)')}
assert all(normalize(original)!=normalize(s) for s in mutations.values())
# The wrapper's only loop tests one seed length; no post-loop explicit return/? pattern.
assert 'for seed in seeds.iter()' in create and 'if seed.len() > MAX_SEED_LEN' in create
assert 'return Err(PubkeyError::MaxSeedLengthExceeded)' in create
x=dict(files=files,tail_identity=True,mutations_rejected=list(mutations),actual_zero_one_native='PCG_K019',actual_find_native='PCG_K003',tail_native='PCG_K020',validation_native='PCG_K022',create_loop='one native iteration; Lean list induction; tail source-fission',trust='ReviewedTranscription PCG-RT-SdkPda; option-A P6/D188 reclassification, not removal',features=dict(solana_pubkey=['borsh','bytemuck','curve25519','serde','sha2','std'],solana_define_syscall=[]),target_cfg='solana_pubkey target_os=solana only; frozen target-specific syscall dependency compiled privately')
(B/'PCG_SDK_SOURCE.json').write_text(json.dumps(x,indent=1)+'\n')
print('PCG SDK source identity and four rejecting mutations pass')
