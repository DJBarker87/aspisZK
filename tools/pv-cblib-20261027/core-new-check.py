from pathlib import Path
import re,json,hashlib
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-cblib-20261027'
ref=(root/'tools/pv-cblib-20261027/lib.rs').read_text();src=(out/'source/sha2-0.10.9__src__core_api.rs').read_text();const=(out/'source/sha2-0.10.9__src__consts.rs').read_text()
body=src[src.index('        let state = match output_size {'):src.index('\n    #[inline]\n    fn finalize_variable_core')];body=body[:body.rindex('\n    }')]
rbody=ref[ref.index('    let state = match output_size {',ref.index('pub fn sha_core_new_owned')):];rbody=rbody[:rbody.index('\n}')]
original_body=body
ports=[]
for n,size in [('H256_224',28),('H256_256',32)]:
 m=re.search(r'pub const '+n+r':[^=]+=\s*\[([^]]+)\]',const);assert m,n
 values=[int(x.strip().replace('_',''),0) for x in m[1].split(',') if x.strip()]
 rm=re.search(str(size)+r' => (\[[^]]+\])',rbody);assert rm
 rvalues=[int(x.strip().replace('_',''),0) for x in rm[1][1:-1].split(',') if x.strip()]
 assert values==rvalues,(n,values,rvalues)
 body=body.replace('consts::'+n,rm[1]);ports.append(n+' exact eight-word constant substitution')
body=body.replace('InvalidOutputSize','InvalidOutputSizeOwned').replace('Self {','ShaCoreOwned {')
normal=lambda s:re.sub(r'\s+','',s)
assert normal(body)==normal(rbody),(body,rbody)
r=dict(status='PASS',original_body_sha256=hashlib.sha256(original_body.encode()).hexdigest(),owned_body_sha256=hashlib.sha256(rbody.encode()).hexdigest(),ports=ports+['Self -> field-identical ShaCoreOwned','empty InvalidOutputSize -> empty InvalidOutputSizeOwned','function/trait namespace erased'],scope='constructor body only, not op217 wrapper/default/Drop closure; no P6 native link claimed')
(out/'core-new-byte-check.json').write_text(json.dumps(r,indent=2)+'\n');print(r['status'])
