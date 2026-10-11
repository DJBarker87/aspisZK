#!/usr/bin/env python3
"""Preserve exact measured-stage source variants as JSON, without any rerun."""
import hashlib,json,subprocess
from pathlib import Path
root=Path(__file__).resolve().parent.parent
out=root/'results/r1-precheck-20261010'
sha=lambda b:hashlib.sha256(b).hexdigest()
w=(root/'crates/aspis-r1-cost-probe/src/weights.rs').read_text()
start=w.index('    #[inline(never)]\n    fn dense_point_pair(')
end=w.index('    pub fn materialize',start)
w2=w[:start]+w[end:]
old='''                let mut rows=aspis_core::r0::heap::filled(1024,K::ZERO).map_err(|_|Error::Allocation)?;
                rows[0]=K::ONE;let mut width=1;
                for b in 0..10 {
                    let p=self.points[kind-1][9-b];
                    for j in (0..width).rev() { let x=rows[j];rows[j+width]=x.mul(p);rows[j]=x.mul(K::ONE.sub(p)); }
                    width*=2;
                }
                for j in 0..n {
                    let mut w=E::ZERO;
                    for s in 0..(1<<(2*folds)) {
                        let p=ap0[PERM[s%4]].mul(ap1[PERM[s/4]]);
                        w=w.add(p.mul_qm31(rows[self.variant.row((j<<(2*folds))+s)]));
                    }
                    for _ in 0..folds {w=w.mul_m31(QUARTER);}
                    parts[kind]=parts[kind].add(field(f,j).mul(w));
                }
'''
w2=w2.replace('                parts[kind]=self.dense_point_pair(kind,alpha,f)?;\n',old)
start=w2.index('            // Two-fold 0/1 row:')
end=w2.index('            for j in 0..4 {parts[4]',start)
w1=w2[:start]+'            for j in 0..n {parts[0]=parts[0].add(field(f,j).mul(self.dual_raw(0,j,alpha)));}\n'+w2[end:]
s=(root/'crates/aspis-r1-cost-probe/src/r1_semantic.rs').read_text()
s=s.replace('    #[cfg(feature="prover")]\n    pub','    pub').replace('    #[cfg(feature="prover")]\n    let mut round_checks','    let mut round_checks')
s=s.replace('        #[cfg(feature="prover")]\n        { round_checks[round] = [running, boundary, value]; }','        round_checks[round] = [running, boundary, value];')
s=s.replace('    #[cfg(feature="prover")]\n    {\n','').replace('    }\n    if z0 == z1','    if z0 == z1')
s=s.replace('        #[cfg(feature="prover")] round_checks,\n        #[cfg(feature="prover")] terminal,\n        #[cfg(feature="prover")] masked_terminal })','        round_checks, terminal, masked_terminal })')
candidates={sha(x.encode()):x for x in [w1,w2,s]}
stages=['semantic-gate-v1','s1-native-compile-v2','s1-sbf-build-v2','driver-build-v1','s2-native-build-v1','s2-sbf-build-v1','d-native-build-v1','d-sbf-build-v1']
blobs={};records=[]
for stage in stages:
    path=out/(stage+'-source-manifest.json')
    manifest=json.loads(path.read_text());overrides={}
    for name,expected in manifest['files'].items():
        current=(root/name).read_bytes()
        if sha(current)==expected:continue
        text=candidates.get(expected)
        if text is None:
            prior=subprocess.run(['git','show','19d8f2023:'+name],cwd=root,capture_output=True)
            if prior.returncode==0 and sha(prior.stdout)==expected:text=prior.stdout.decode()
        assert text is not None,(stage,name,expected,sha(current))
        assert sha(text.encode())==expected
        blobs[expected]=text;overrides[name]=expected
    records.append({'stage':stage,'source_manifest':path.name,'source_manifest_sha256':sha(path.read_bytes()),'exact_file_overrides':overrides,'every_manifest_hash_checked':True})
(out/'source-replay.json').write_text(json.dumps({'label':'UNPROVED COST PROBE; exact stage-source retention, no execution','base_for_unchanged_files':'final task tree; reference paths unchanged from 600eb0138','stages':records,'utf8_blobs_by_sha256':blobs},indent=2)+'\n')
print(json.dumps({'stages':len(records),'retained_source_variants':len(blobs),'all_source_hashes_checked':True}))
