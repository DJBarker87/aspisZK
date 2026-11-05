import sys,json,hashlib,re
from pathlib import Path
sys.dont_write_bytecode=True
from NIZ_native_prepare import stage,attrs
from NIZ_frozen_identity import frozen
E=Path(__file__).resolve().parent
mode=sys.argv[1]
p='programs/aspis-pool/src/transition.rs';text=frozen()[p].decode();line=text.splitlines()[863];assert '|| Ok(())' in line
name='certificate_stability' if mode=='stability' else 'certificate'
callback='|| Ok(())'
if mode=='frame-negative':callback='|| {observer^=1;Ok(())}'
if mode=='reply-negative':callback='|| Err(solana_program::program_error::ProgramError::InvalidArgument)'
source='fn NIZ_invoke<F:FnOnce()->solana_program::entrypoint::ProgramResult>(f:F)->solana_program::entrypoint::ProgramResult{f()}\n'+attrs()+'\n#[kani::proof]\nfn '+name+'(){let mut observer:u8=kani::any();let before=observer;let result=NIZ_invoke('+callback+');assert!(result.is_ok());assert!(observer==before);}\n'
stage('programs/aspis-pool/src/transition.rs',source,'deployed no-op before_persist instantiation under (al)',mode,'Capture-free deployed closure at transition.rs:864; arbitrary observed byte for exact empty-footprint frame; no function pointer value or comparison.','Must bind this callee footprint at actual transition wrapper call sites; no complete parent ScopeRun.',dict(expected_verdict='FAIL' if 'negative' in mode else 'PASS',member='noop_before_persist',native_args=['--unwind','2'],harness='transition::NIZ_native::'+name,source_literal_sha256=hashlib.sha256(b'|| Ok(())').hexdigest(),source_file_sha256=hashlib.sha256(text.encode()).hexdigest(),source_line=864,rule_al=True,rename_stability=mode=='stability'))
