"""Lift only nested function declarations; preserve exact body tokens and imports.
Full owned terminal is an unchanged prefix for method-root extraction.
"""
from pathlib import Path
import hashlib,json
T=Path('tools/pv-b3p6-20261028');old=T/'v244';new=T/'v244-missing14';new.mkdir(exist_ok=True)
sha=lambda b:hashlib.sha256(b).hexdigest()
s=(old/'reference_terminal.rs').read_text()
def decl(mark):
 a=s.index(mark);b=s.index('{',a);depth=1;i=b+1
 while depth:
  depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return a,i,s[a:i]
a,b,fields=decl('fn fields(out:');c,d,frontier=decl('fn frontier(out:')
manifest=(old/'Cargo.toml').read_text().split('[[bin]]')[0]+(old/'Cargo.toml').read_text().split('[dependencies]')[1].split('[[bin]]')[0]
# Keep all original dependency pins, features and release profile, drop binaries.
manifest=(old/'Cargo.toml').read_text();manifest=manifest.replace('[[bin]]\nname="finite227"\npath="finite227.rs"\n','');manifest=manifest.split('[[bin]]')[0]
(new/'Cargo.toml').write_text(manifest)
(new/'host_terminal_constants.rs').write_bytes((old/'host_terminal_constants.rs').read_bytes())
(new/'original_poseidon14.rs').write_bytes(Path('crates/aspis-statement/src/state_only_poseidon.rs').read_bytes())
# Deployed resolved lock is copied from the verified host workspace by extraction wrapper.
(new/'reference_terminal.rs').write_text(s+'\n#[cfg(feature="prover")]\npub fn terminal_root14(p:r0::Public<\'_>,claims:&[[QM31;29];3],point:&[QM31;10],c:&aspis_core::state_only_prefix::r0::Challenges)->Result<QM31,aspis_core::state_only_prefix::r0::Error>{p.terminal_qm31(claims,point,c)}\n#[cfg(feature="prover")]\npub fn transition_root14(p:r0::Public<\'_>)->&PoolV1PairLatePublicStatementV1{p.transition()}\n')
lib=(old/'lib.rs').read_text();lib=lib.replace('mod reference_terminal;', 'mod reference_terminal;')
for name in ['host_terminal_field.rs','host_copy_terminal.rs','host_terminal.rs','reference_field.rs','reference_copy_terminal.rs','reference_poseidon.rs','std194227.rs']:
 lib=lib.replace('mod '+name[:-3]+';', '#[path="../v244/'+name+'"] mod '+name[:-3]+';')
lib=lib.replace('pub #[path=', '#[path=').replace('] mod host_terminal;', '] pub mod host_terminal;').replace('] mod std194227;', '] pub mod std194227;')
(new/'lib.rs').write_text(lib+'\nuse aspis_core::field::M31;\nuse aspis_core::state_only_prefix::r0::Error;\nuse aspis_statement::poseidon2::Digest;\nuse alloc::vec::Vec;\n'+fields.replace('fn fields','pub fn fields',1)+'\n'+frontier.replace('fn frontier','pub fn frontier',1)+'\n')
record=dict(owned_file=str(old/'reference_terminal.rs'),owned_sha256=sha(s.encode()),unchanged_prefix_sha256=sha((new/'reference_terminal.rs').read_bytes()[:len(s.encode())]),lifts=[dict(name=n,start_byte=x,end_byte=y,body_sha256=sha(z[z.index('{'):].encode()))for n,x,y,z in [('fields',a,b,fields),('frontier',c,d,frontier)]],scope='Nested declarations relocated verbatim; only pub visibility added outside function body. Same M31, Digest, Error, Vec paths; frontier resolves to the exact lifted fields. No output editing.')
Path('evidence/pv-b3p6-20261028/resume14/lift-inputs.json').write_text(json.dumps(record,indent=2)+'\n')

p=new/'lib.rs';p.write_text(p.read_text()+'\npub use aspis_statement::poseidon2;\npub mod original_poseidon14;\n')
