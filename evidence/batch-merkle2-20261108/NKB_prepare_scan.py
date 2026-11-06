from pathlib import Path
import json,hashlib,lzma,base64
E=Path(__file__).resolve().parent
raw=base64.b64decode(json.loads(lzma.decompress((E/'NKB_FROZEN_PAYLOAD.json.xz').read_bytes()))['crates/aspis-r1-cost-probe/src/candidate.rs']).decode()
print(raw[raw.index('fn canonical_scan'):raw.index('fn canonical_scan')+1600])
fr=E/'NKB_fragments.rs';ha=E/'NKB_harness.rs';assoc=json.loads((E/'NKB_FRAGMENT_ASSOCIATION.json').read_text())
for name,line,args in [
 ('scan_scalar','                M31::from_le_bytes(q[s * 120 + l * 4..s * 120 + l * 4 + 4].try_into().unwrap()).ok_or(Error::Parse)?;','q:&[u8],s:usize,l:usize'),
 ('scan_c1','            K::from_le_bytes(&q[s * 120 + 104..s * 120 + 120]).ok_or(Error::Parse)?;','q:&[u8],s:usize'),
 ('scan_c2','                K::from_le_bytes(&q[480 + s * 32 + l * 16..480 + s * 32 + l * 16 + 16]).ok_or(Error::Parse)?;','q:&[u8],s:usize,l:usize')]:
 assert line in raw
 with fr.open('a') as f:f.write('\nfn '+name+'_fragment('+args+')->Result<(),Error>{\n'+line+'\nOk(())\n}\n')
 assoc['spans'].append(dict(body=line,sha256=hashlib.sha256(line.encode()).hexdigest(),source='crates/aspis-r1-cost-probe/src/candidate.rs'))
 harness='''
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn NAME(){
 let q:[u8;832]=kani::any();let s:usize=kani::any();kani::assume(s<4);
 LDECL
 let start=START;let out=CALL;
 let w=|j:usize|u32::from_le_bytes([q[start+j],q[start+j+1],q[start+j+2],q[start+j+3]]);
 let expected=EXPECT;
 #[cfg(not(NKB_invert))] assert_eq!(out.is_ok(),expected);
 #[cfg(NKB_invert)] assert_ne!(out.is_ok(),expected);
 if !expected{assert!(matches!(out,Err(Error::Parse)))}
 let observer:usize=kani::any();kani::assume(observer<832);assert_eq!(q[observer],q[observer]);
}
'''
 if name=='scan_scalar':ld='let l:usize=kani::any();kani::assume(l<26);';start='s*120+l*4';call=name+'_fragment(&q,s,l)';expect='w(0)<2147483647'
 elif name=='scan_c1':ld='';start='s*120+104';call=name+'_fragment(&q,s)';expect='w(0)<2147483647&&w(4)<2147483647&&w(8)<2147483647&&w(12)<2147483647'
 else:ld='let l:usize=kani::any();kani::assume(l<2);';start='480+s*32+l*16';call=name+'_fragment(&q,s,l)';expect='w(0)<2147483647&&w(4)<2147483647&&w(8)<2147483647&&w(12)<2147483647'
 for a,b in [('NAME',name),('LDECL',ld),('START',start),('CALL',call),('EXPECT',expect)]:harness=harness.replace(a,b)
 # Immutable shared input needs no vacuous self-frame assertion.
 harness=harness.replace(' let observer:usize=kani::any();kani::assume(observer<832);assert_eq!(q[observer],q[observer]);\n','')
 with ha.open('a') as f:f.write(harness)
(E/'NKB_FRAGMENT_ASSOCIATION.json').write_text(json.dumps(assoc,indent=2)+'\n')
base=json.loads((E/'NKB_K021.json').read_text())
for n,name in [(23,'scan_scalar'),(25,'scan_c1'),(27,'scan_c2')]:
 for num,neg in [(n,False),(n+1,True)]:
  x=json.loads(json.dumps(base));a=f'NKB_K{num:03d}';x.update(attempt=a,module=name,expected_failure=neg,collect=[a+'_validation'],env=json.loads((E/'NKB_ENV.json').read_text()),expected_time='Single canonical_scan source read; actual small decoder; no multiplication or whole-loop unwind')
  x['command']=['python3','NKB_gate.py',a+'.json'];x['native_command'][x['native_command'].index('--harness')+1]='verifier::candidate::NKB_native::'+name
  if neg:x['env']['RUSTFLAGS']=x['env'].get('RUSTFLAGS','')+' --cfg NKB_invert'
  (E/(a+'.json')).write_text(json.dumps(x,indent=2)+'\n')
