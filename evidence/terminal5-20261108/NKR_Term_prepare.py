from pathlib import Path
import subprocess,json,hashlib,difflib,re
E=Path(__file__).resolve().parent
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';source='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs'
old=subprocess.check_output(['git','show',rev+':'+source],text=True);code=(E/'NKR_Term_native.rs.txt').read_text()
def body(s,name):
 p=s.index('fn '+name+'(');p=s.index('{',p);q=p+1;d=1
 while d:d+=(s[q]=='{')-(s[q]=='}');q+=1
 return s[p+1:q-1]
b=body(old,'terminal_parts');start=b.index('    let original =');suffix=b[start:]
expected='''let original = equality_value(zerocheck_point, point)
        .mul(composition)
        .add(mu.mul(h1_z))
        .add(mu.mul(mu).mul(QM31::ONE.sub(copy_active).mul(h1_z)));
    Ok((original, c1, mask_only, g))'''
compact=lambda s:re.sub(r'\s+','',s)
assert compact(suffix)==compact(expected),'Frozen suffix changed'
translated='''let (composition, c1, mask_only, g, h1_z, copy_active) = child?;
let original = NKR_tadd(NKR_tadd(NKR_tmul(NKR_teq(zerocheck_point,point,l),composition,l),NKR_tmul(mu,h1_z,l),l),NKR_tmul(NKR_tmul(mu,mu,l),NKR_tmul(NKR_tsub(QM31::ONE,copy_active,l),h1_z,l),l),l);
Ok((original, c1, mask_only, g))'''
assert compact(body(code,'NKR_term_suffix'))==compact(translated),'Native window changed'
name='crates/aspis-statement/src/pool_v1/NKR_Term_native.rs';new=old+'\n#[cfg(kani)]\n#[path="NKR_Term_native.rs"]\nmod NKR_term_native;\n'
patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+source,tofile='b/'+source))
patch+=''.join(difflib.unified_diff([],code.splitlines(True),fromfile='/dev/null',tofile='b/'+name))
(E/'NKR_Term_native.patch').write_text(patch)
(E/'NKR_Term_TRANSCRIPTION.json').write_text(json.dumps(dict(revision=rev,source=source,source_sha256=hashlib.sha256(old.encode()).hexdigest(),harness_sha256=hashlib.sha256(code.encode()).hexdigest(),frozen_suffix=suffix,translated=translated,native=body(code,'NKR_term_suffix'),identity=True,order=['equality','mul','mul','add','mul','sub','mul','mul','add'],coverage='Complete SAME composition tuple/Err child; actual parent237 call arguments remain a separate caller prefix window'),indent=2))
print('Terminal263 suffix frozen expression tree and full Result transcription PASS')
