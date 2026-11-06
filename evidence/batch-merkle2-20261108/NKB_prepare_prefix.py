from pathlib import Path
import json,lzma,base64,hashlib
E=Path(__file__).resolve().parent
raw=base64.b64decode(json.loads(lzma.decompress((E/'NKB_FROZEN_PAYLOAD.json.xz').read_bytes()))['crates/aspis-r1-cost-probe/src/candidate.rs']).decode()
body=raw[raw.index('    compact::check_values',raw.index('fn canonical_scan')):raw.index('    for i in 0..22',raw.index('fn canonical_scan'))].rstrip()
p=E/'NKB_fragments.rs';assert 'fn scan_prefix_fragment' not in p.read_text();p.write_text(p.read_text()+'\nfn scan_prefix_fragment(proof:&[u8])->Result<(),Error>{\n'+body+'\nOk(())\n}\n')
a=json.loads((E/'NKB_FRAGMENT_ASSOCIATION.json').read_text());a['spans'].append(dict(body=body,sha256=hashlib.sha256(body.encode()).hexdigest(),source='crates/aspis-r1-cost-probe/src/candidate.rs'));(E/'NKB_FRAGMENT_ASSOCIATION.json').write_text(json.dumps(a,indent=2)+'\n')
h='''
fn scan_compact_ok(bytes:&[u8])->Result<(),compact::CodecError>{assert_eq!(bytes.len(),464);Ok(())}
fn scan_compact_reject(bytes:&[u8])->Result<(),compact::CodecError>{assert_eq!(bytes.len(),464);Err(compact::CodecError::NonCanonical)}
fn scan_prefix_ok(bytes:&[u8],k:bool)->Result<(),Error>{assert!(!k);assert!(bytes.len()==32||bytes.len()==224||bytes.len()==2272);Ok(())}
fn scan_prefix_forbid(_:&[u8],_:bool)->Result<(),Error>{assert!(false,"no suffix after compact rejection");Ok(())}
'''
for length in [32,224,2272]:
 h+=f'fn scan_prefix_reject{length}(bytes:&[u8],k:bool)->Result<(),Error>{{assert!(!k);assert!(bytes.len()==32||bytes.len()==224||bytes.len()==2272);assert!(bytes.len()<={length},"no echeck suffix after rejection");if bytes.len()=={length}{{Err(Error::Parse)}}else{{Ok(())}}}}\n'
for name,cv,ec,good in [('scan_prefix_ok_case','scan_compact_ok','scan_prefix_ok',True),('scan_prefix_cv_reject','scan_compact_reject','scan_prefix_forbid',False)]+[(f'scan_prefix_reject{n}_case','scan_compact_ok',f'scan_prefix_reject{n}',False) for n in [32,224,2272]]:
 expect='out.is_ok()' if good else 'matches!(out,Err(Error::Parse))'
 h+=f'''#[kani::proof]
#[kani::unwind(2)]
#[kani::stub(compact::check_values,{cv})]
#[kani::stub(echeck,{ec})]
fn {name}(){{let proof:[u8;57607]=kani::any();let out=scan_prefix_fragment(&proof);
 #[cfg(not(NKB_invert))] assert!({expect});
 #[cfg(NKB_invert)] assert!(!{expect});
}}
'''
with (E/'NKB_harness.rs').open('a') as f:f.write(h)
names=['scan_prefix_ok_case','scan_prefix_cv_reject']+[f'scan_prefix_reject{n}_case' for n in [32,224,2272]]
for n,name in zip([39,41,43,45,47],names):
 for num,old in [(n,29),(n+1,30)]:
  x=json.loads((E/f'NKB_K{old:03d}.json').read_text());a=f'NKB_K{num:03d}';x.update(attempt=a,module=name,collect=[a+'_validation']);x['command']=['python3','NKB_gate.py',a+'.json'];x['native_command'][x['native_command'].index('--harness')+1]='verifier::candidate::NKB_native::'+name;(E/(a+'.json')).write_text(json.dumps(x,indent=2)+'\n')
print('Prepared five prefix constructor cases and matched controls; no count/payload-log assertion added')
