from NMD_program import *
(E/'NMD_program.rs').write_text((E/'NMD_shape_program.rs').read_text()+'''\n#[kani::proof]#[kani::unwind(4)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_copy_control(){let src:[u8;2]=kani::any();let mut dst=[0u8;2];dst.copy_from_slice(&src);assert!(dst[1]!=src[1]);}
''')
for i,name in enumerate(['NMD_contract','NMD_inverse','NMD_real','NMD_unimplied','NMD_modifies','NMD_copy_control'],int(sys.argv[1]) if len(sys.argv)>1 else 51):
 a=f'NMD_K{i:03}';r=native(a,'r1_pool_adapter::owned::NMD_program::'+name)
 log=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode();assert 'Traceback' not in log and 'Failed to match' not in log,'OWN INPUT ERROR; stop this queue before another launch'
 verdict='TIMEOUT' if 'timed out' in log.lower() else 'FAILED' if 'VERIFICATION:- FAILED' in log else 'COMPILE_OR_GATE_ERROR' if r['exit_status'] else 'SUCCESSFUL'
 with (E/'NMD_SHAPE_RESULTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,shape='ProgramResult',control=name,exit_status=r['exit_status'],verdict=verdict))+'\n')
