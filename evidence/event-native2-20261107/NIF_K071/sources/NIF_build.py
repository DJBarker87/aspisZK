from pathlib import Path
import json,hashlib,difflib,re
B=Path(__file__).resolve().parent
def write(p,t):
 if not p.exists() or p.read_text()!=t:p.write_text(t)
def build():
 f=json.loads((B/'NIF_FROZEN.json').read_text());S=B/'NIF_src'
 for n,t in f.items():
  p=S/n
  if p.is_file():
   if n=='Cargo.lock':assert p.read_text()==t,'lock drift'
   elif n not in ['crates/aspis-r1-cost-probe/src/verifier.rs','crates/aspis-r1-cost-probe/src/candidate.rs','programs/r1-cost-probe/src/lib.rs','crates/aspis-r1-cost-probe/src/lib.rs','crates/aspis-r1-cost-probe/src/transcript.rs','crates/aspis-r1-cost-probe/src/fast_dots.rs']:write(p,t)
 patch=(B/'NIF_KMX.patch').read_text();assert hashlib.sha256(patch.encode()).hexdigest()=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 for part in patch.split('diff --git ')[1:]:
  n=part.splitlines()[0].split(' b/')[1];write(S/n,'\n'.join(l[1:] for l in part.splitlines() if l.startswith('+') and not l.startswith('+++'))+'\n')
 additions={
 'crates/aspis-r1-cost-probe/src/fast_dots.rs':'\n#[cfg(kani)] pub mod NIF_dots { include!("NIF_dots.rs"); }\n',
 'crates/aspis-r1-cost-probe/src/transcript.rs':'\n#[cfg(kani)] pub mod NIF_transcript { include!("NIF_transcript.rs"); }\n',
 'crates/aspis-r1-cost-probe/src/verifier.rs':'\n#[cfg(kani)] pub mod NIF_native { include!("NIF_native.rs"); }\n',
 'crates/aspis-r1-cost-probe/src/candidate.rs':'\n#[cfg(kani)] pub mod NIF_opening { include!("NIF_opening.rs"); }\n',
 'programs/r1-cost-probe/src/lib.rs':'\n#[cfg(kani)] mod NIF_purity { include!("NIF_purity.rs"); }\n'}
 for n,t in additions.items():write(S/n,(f[n].replace('use aspis_r1_cost_probe::', '#![cfg_attr(kani,recursion_limit="256")]\nuse aspis_r1_cost_probe::',1) if n=='programs/r1-cost-probe/src/lib.rs' else f[n])+t)
 n='crates/aspis-r1-cost-probe/src/lib.rs';write(S/n,f[n].replace('#![no_std]','#![no_std]\n#![cfg_attr(kani,feature(allocator_api))]')+'\n#[cfg(kani)] pub mod NIF_copy { include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs")); }\n')
 owned={
 'crates/aspis-r1-cost-probe/src/NIF_dots.rs':'NIF_dots.rs.txt',
 'crates/aspis-r1-cost-probe/src/NIF_transcript.rs':'NIF_transcript.rs.txt',
 'crates/aspis-r1-cost-probe/src/NIF_native.rs':'NIF_native.rs.txt',
 'crates/aspis-r1-cost-probe/src/NIF_opening.rs':'NIF_opening.rs.txt',
 'programs/r1-cost-probe/src/NIF_purity.rs':'NIF_purity.rs.txt'}
 for dst,src in owned.items():write(S/dst,(B/src).read_text())
 changed={n:hashlib.sha256((S/n).read_bytes()).hexdigest() for n,t in f.items() if (S/n).is_file() and (S/n).read_text()!=t}
 out=''.join(''.join(difflib.unified_diff(t.splitlines(True),(S/n).read_text().splitlines(True),fromfile='a/'+n,tofile='b/'+n)) for n,t in f.items() if (S/n).is_file() and (S/n).read_text()!=t)
 for n in owned:out+=''.join(difflib.unified_diff([],(S/n).read_text().splitlines(True),fromfile='/dev/null',tofile='b/'+n))
 (B/'NIF_harness.patch').write_text(out)
 assert all((S/n).read_text()==(f[n].replace('use aspis_r1_cost_probe::', '#![cfg_attr(kani,recursion_limit="256")]\nuse aspis_r1_cost_probe::',1) if n=='programs/r1-cost-probe/src/lib.rs' else f[n])+t for n,t in additions.items())
 return dict(erasure_exact=True,changed=changed,owned={n:hashlib.sha256((S/n).read_bytes()).hexdigest() for n in owned},qualification='Native syscall-unreachability only; no value bridge replacement')
