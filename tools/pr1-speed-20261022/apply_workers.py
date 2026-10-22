"""Apply stage 3 only after the stage-2 gate decision."""
from pathlib import Path
r=Path(__file__).resolve().parents[2];c=r/'docs/research/v8-r0-zk-20261009/c3'
(c/'check/src/native_workers.rs').write_bytes((r/'tools/pr1-speed-20261022/worker-template.rs.txt').read_bytes())
# Both crates use the same worker/TLS implementation and state via a dependency.
p=c/'check/Cargo.toml';s=p.read_text();s+=('native-workers = ["native-kernels"]\n' if 'native-kernels' in s else '\n[features]\nnative-workers = []\n');p.write_text(s)
p=c/'build/Cargo.toml';s=p.read_text();s+=('native-workers = ["native-kernels", "dep:aspis-r1-cert-check"]\n' if 'native-kernels' in s else '\n[features]\nnative-workers = ["dep:aspis-r1-cert-check"]\n');s+='\n[dependencies]\naspis-r1-cert-check = {path="../check",features=["native-workers"],optional=true}\n';p.write_text(s)
p=c/'check/src/lib.rs';s=p.read_text();s+='\n#[cfg(feature="native-workers")]\npub mod native_workers;\n'
a=s.index('    let mut ok = true;',s.index('pub fn prod_ok('));s=s[:a]+'''    #[cfg(feature="native-workers")]
    if ni <= 1 << 20 && ni >= native_workers::THREADS*2 {
        return native_workers::ordered_map(ni, |i| prod_row_ok(a,ao,b,bo,c,co,i,nj,len)).into_iter().fold(true, |a,b| a & b);
    }
'''+s[a:]
# Reuse the entry function on a one-element descriptor subslice; all underlying
# indexed source matrices and pivot offsets remain unchanged.
a=s.index('    let mut ok = true;',s.index('pub fn ents_ok('));s=s[:a]+'''    #[cfg(feature="native-workers")]
    if !native_workers::is_worker() && m >= native_workers::THREADS*2 && m <= 1 << 20 {
        return native_workers::ordered_map(m, |e| ents_ok(&ej[e..e+1],&es[e..e+1],&epo[e..e+1],&eco[e..e+1],idx,coef,1,lane,wl,z1,s1,z2,s2,n2,g,sg,ng,&out[e*ng..],zero)).into_iter().fold(true, |a,b| a & b);
    }
'''+s[a:]
# The recursion must NOT manufacture a suffix access when ng==0: out[e*0..]
# is always out[0..], same as the original zero-row observation.
p.write_text(s)
p=c/'build/src/lib.rs';s=p.read_text()
for f,number,expr in [
 ('fill_own','n','own_col(Vec::new(), al,zz,tr,sx,sy,inact,kind[t] as usize,srow[t] as usize,slimb[t] as usize,os,24+4*nq,24+16*nq)'),
 ('fill_round','n','round_col(Vec::new(),al,tr,inact,kind[t] as usize,srow[t] as usize,slimb[t] as usize)'),
 ('fill_gbat','n','gbat_col(Vec::new(),al,zz,tr,inact,ti,op,x18,nf,srow[t] as usize,slimb[t] as usize)'),
 ('fill_rel','q','rel_row(Vec::new(),al,zz,tr,inact,ti,op,fpos,rk,ru,li,x16,nf,t)')]:
 a=s.index('{',s.index('pub fn '+f+'('))+1
 s=s[:a]+f'''\n    #[cfg(feature="native-workers")]
    if {number} <= 1 << 20 {{ return aspis_r1_cert_check::native_workers::ordered_map({number}, |t| {expr}).into_iter().flatten().collect(); }}'''+s[a:]
p.write_text(s)
p=r/'docs/research/v8-r0-zk-20261009/z4/Cargo.toml';s=p.read_text().replace('features = ["native-kernels"]','features = ["native-workers"]');s=s.replace('{ path = "../c3/check" }','{ path = "../c3/check", features = ["native-workers"] }').replace('{ path = "../c3/build" }','{ path = "../c3/build", features = ["native-workers"] }');p.write_text(s)
p=r/'docs/research/v8-r0-zk-20261009/z4/z9d.rs';s=p.read_text()
for f,var,count,rows,sel in [('fq','rho','m','RW','round'),('fg','beta','mg','bwr','bat')]:
 import re
 pattern=r'    let mut '+var+r' = Vec::with_capacity\([^\n]+\);\n    for (e2?) in 0\.\.'+count+r' \{\n        '+var+r'\.extend\(image\(&'+f+r', \1, '+rows+r', &\|s\| &s\.'+sel+r'\)\);\n    \}'
 s,n=re.subn(pattern,'    let '+var+' = ck::native_workers::ordered_map('+count+', |entry| image(&'+f+',entry,'+rows+',&|s| &s.'+sel+')).into_iter().flatten().collect();',s);assert n,var
p.write_text(s)
p=r/'docs/research/v8-r0-zk-20261009/z4/z9e.rs';s=p.read_text().replace('if !QUIET.with(|q| q.get()) {','if !QUIET.with(|q| q.get()) && !ck::native_workers::is_worker() {');p.write_text(s)

p=r/'docs/research/v8-r0-zk-20261009/z4/z9c.rs';s=p.read_text()
s=s.replace('targets.iter().map(|b| rech.express(b.clone())).collect()', 'aspis_r1_cert_check::native_workers::ordered_map(targets.len(), |i| rech.express(targets[i].clone())).into_iter().collect()')
s=s.replace('nvec.iter().map(|n| vech.express(n.clone())).collect()', 'aspis_r1_cert_check::native_workers::ordered_map(nvec.len(), |i| vech.express(nvec[i].clone())).into_iter().collect()')
p.write_text(s)
for name in ['Cargo.lock','docs/research/v8-r0-zk-20261009/z4/Cargo.lock']:
 p=r/name;s=p.read_text();before='name = "aspis-r1-cert-build"\nversion = "0.0.0"\n';assert s.count(before)==1
 s=s.replace(before,before+'dependencies = [\n "aspis-r1-cert-check",\n]\n');p.write_text(s)
