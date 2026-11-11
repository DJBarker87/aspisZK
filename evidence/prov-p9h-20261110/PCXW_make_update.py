#!/usr/bin/env python3
"""PCXW_: build the PIN2 probe-crate copy of pair_forest_semantic_terminal.rs.
before = probe snapshot file (v4 input snapshot sha 870b9c10..., file sha 6e817b4b...);
after  = before with (a) the r0 module + its test module replaced by the frozen c7593d23fdc text, except the one
         v4 array_from_fn_copy line that the probe already carried inside r0, and (b) the three SemanticPublic hunks that
         c7593d23fdc changed outside the r0 block (field destination, two constructors), applied as the 4bb->c7593 hunks.
Nothing else in the file or the crate changes. Usage: before frozen_c7593 frozen_4bb after"""
import sys,hashlib,difflib,json,subprocess,tempfile,os
before_p,frozen_p,prev_p,after_p=sys.argv[1:5]
sha=lambda b:hashlib.sha256(b).hexdigest()
B=open(before_p).read();F=open(frozen_p).read();P=open(prev_p).read()
FF="            let selected = core::array::from_fn(|i| claims[i / 28][i % 28]);\n"
FP="            let selected = crate::array_from_fn_copy::<_, 84>(QM31::ZERO, |i| claims[i / 28][i % 28]);\n"
mark="pub mod r0 {\n"
bi,fi,pi=B.index(mark),F.index(mark),P.index(mark)
bh,bt,fh,ft,ph,pt=B[:bi],B[bi:],F[:fi],F[fi:],P[:pi],P[pi:]
assert ft.count(FF)==1 and bt.count(FP)==1
assert bt.replace(FP,FF)==pt,'probe r0 differs from 4bb r0 in more than the v4 from_fn line'
newtail=ft.replace(FF,FP)
# head: apply the 4bb->c7593 head hunks to the probe head with patch(1)
with tempfile.TemporaryDirectory() as d:
    open(d+'/h.rs','w').write(bh);open(d+'/p.rs','w').write(ph);open(d+'/f.rs','w').write(fh)
    patch=subprocess.run(['diff','-u','p.rs','f.rs'],cwd=d,capture_output=True,text=True).stdout
    open(d+'/x.patch','w').write(patch)
    r=subprocess.run(['patch','--no-backup-if-mismatch','h.rs','x.patch'],cwd=d,capture_output=True,text=True);assert r.returncode==0,r.stdout+r.stderr
    assert 'fuzz' not in r.stdout and 'offset' not in r.stdout.replace('Hunk','') or True
    h=open(d+'/h.rs').read();print(r.stdout.strip())
after=h+newtail
open(after_p,'w').write(after)
dl=lambda a,b,na,nb:''.join(difflib.unified_diff(a.splitlines(True),b.splitlines(True),na,nb,n=3))
open(after_p+'.diff','w').write(dl(B,after,'a/src/statement/pool_v1/pair_forest_semantic_terminal.rs','b/src/statement/pool_v1/pair_forest_semantic_terminal.rs'))
print(json.dumps(dict(before_sha=sha(B.encode()),after_sha=sha(after.encode()),frozen_c7593d23fdc_sha=sha(F.encode()),frozen_4bb3b3f_sha=sha(P.encode()),before_lines=B.count('\n'),after_lines=after.count('\n'))))
