from NMD_native import *
import shutil,os
start=int(sys.argv[1]) if len(sys.argv)>1 else 4
shape_list=sys.argv[2:] or ['plain','unit','box','ref','refmut']
a=start
for shape in shape_list:
 src=(E/('NMD_shape_'+shape+'.rs')).read_text()
 if os.environ.get('NMD_ENUMS')=='1':src+=(E/'NMD_ENUM_ARBITRARY.rs').read_text()
 src+='''
#[kani::proof]#[kani::unwind(4)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_copy_control() {let src:[u8;2]=kani::any();let mut dst=[0u8;2];dst.copy_from_slice(&src);assert!(dst[1]!=src[1]);}
'''
 (E/'NMD_native.rs').write_text(src)
 names=['NMD_inverse','NMD_real','NMD_unimplied','NMD_modifies','NMD_copy_control'] if shape=='plain' and start==4 else ['NMD_contract','NMD_inverse','NMD_real','NMD_unimplied','NMD_modifies','NMD_copy_control']
 for name in names:
  attempt=f'NMD_K{a:03}';a+=1
  r=native(attempt,'verifier::candidate::NMD_native::'+name)
  log=lzma.decompress((E/attempt/'stdout.log.xz').read_bytes()).decode()
  verdict='TIMEOUT' if 'timed out' in log.lower() else 'SUCCESSFUL' if 'VERIFICATION:- SUCCESSFUL' in log or 'VERIFICATION SUCCESSFUL' in log else 'FAILED' if 'VERIFICATION:- FAILED' in log or 'VERIFICATION FAILED' in log else 'COMPILE_OR_GATE_ERROR' if r['exit_status'] else 'SUCCESSFUL'
  record=dict(attempt=attempt,shape=shape,control=name,exit_status=r['exit_status'],verdict=verdict,diagnostic=log[-2300:] if verdict=='COMPILE_OR_GATE_ERROR' else None)
  with (E/'NMD_SHAPE_RESULTS.jsonl').open('a') as f:f.write(json.dumps(record)+'\n')
  # native() emits one concise receipt line; classification is retained in JSONL.
