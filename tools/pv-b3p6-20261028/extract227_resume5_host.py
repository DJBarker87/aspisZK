"""Pinned extraction under ruling x'; native evidence remains on 1.94.1."""
from run import H,run
from pathlib import Path
import hashlib,json,subprocess,sys
p=H/'source/tools/pv-b3p6-20261028/v244'
charon=Path('/home/dombarker/project-offloads/codex-pv-extract-20261027/charon')
aeneas=Path('/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools/aeneas')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(charon)=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
assert sha(aeneas)=='562e1f51ef9bea84f62793f21b4d6b48f9ae65c61ec72588170b2c3abdc37f19'
x=json.loads((H/'features227-resume4.json').read_text());assert x['feature_differences']==[]
llbc=H/'PV_B3P_227_resume5.llbc'
kind=sys.argv[1]
variant=sys.argv[2] if len(sys.argv)>2 else 'original'
if variant!='original':llbc=H/('PV_B3P_227_'+('horner' if variant=='diagnostic' else variant)+'_resume5.llbc')
if kind=='charon':
 cmd=['timeout','300','taskset','--cpu-list','0-3',str(charon),'cargo','--preset','aeneas','--mir','optimized','--sysroot','default','--start-from',('crate::reference_terminal::reference227' if variant in ('owned','ownedread','ownedcall','horner','equality','unrolleq','ranges','sum','value','unrollvalue','digest','digeststate','construct','initial','initiallane','lanes','reconstruct','tweak','copylimb','copyactive','absorb','closure','masks','projected','projected2','projectedloops','projectedsplit','projectedcolumn','parts','composition','stdcone','partsstdcone') else 'crate::reference227' if variant=='entry' else 'crate::reference_terminal::r0::Public::terminal_qm31' if variant!='original' else 'crate::host_terminal::r0::Public::terminal_qm31'),'--include',('pv_b3p6_reference227::reference_terminal::*' if variant!='original' else 'pv_b3p6_reference227::host_terminal::*'),'--include','pv_b3p6_reference227::host_copy_terminal::*','--include','pv_b3p6_reference227::reference_copy_terminal::*','--include','pv_b3p6_reference227::reference_poseidon::*','--include','pv_b3p6_reference227::reference_field::*','--include','pv_b3p6_reference227::host_terminal_field::*','--include','aspis_core::field::*','--dest-file',str(llbc),'--','--manifest-path',str(p/'Cargo.toml'),'--release','--locked','--offline','--lib','--jobs','4']
 if variant in ('masks','projected','projected2','projectedloops','projectedsplit','projectedcolumn','parts','composition','stdcone','partsstdcone'):
  i=cmd.index('--dest-file');cmd[i:i]=['--include','aspis_core::*','--include','aspis_statement::poseidon2::*','--include','aspis_statement::pool_v1::pair_tree_profile::*']
 if variant in ('stdcone','partsstdcone'):
  i=cmd.index('--dest-file');cmd[i:i]=['--include','core::*']
 if variant=='closure':
  i=cmd.index('--dest-file');cmd[i:i]=['--include','aspis_core::*','--include','aspis_statement::*','--include','core::*']
 if variant=='select':
  i=cmd.index('--start-from');cmd[i+1]='crate::reference_terminal::select227'
 if variant=='std194':
  i=cmd.index('--start-from');cmd[i:i+2]=sum((['--start-from','crate::std194227::'+n]for n in ['from_u32_u64','from_bool_u32','from_u16_usize','from_u8_usize']),[])
 sys.exit(run('charon227-resume5-'+variant,cmd,'x-prime extraction on unchanged pinned nightly; deployed dependencies/features and release optimized MIR; expected time in compilation and translation',{'RUSTUP_TOOLCHAIN':'nightly-2026-06-01','CARGO_TARGET_DIR':str(H/'charon-target')}))
if kind=='aeneas':
 out=H/('generated227-resume5-'+variant);out.mkdir(exist_ok=True)
 sys.exit(run('aeneas227-resume5-'+variant,['timeout','300',str(aeneas),'-log-debug','Translate','-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace','PV_B3P_227','-dest',str(out),'-split-files','-emit-json',str(llbc)],'pinned fail-closed Aeneas extraction; strict joins, no bypass or body edits'))
raise AssertionError(kind)
