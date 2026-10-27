# Same pinned commands/admission function; MIR and extraction share one sequential capped scope.
from pathlib import Path
import sys,os,json,runpy,subprocess
D=Path('/home/dombarker/project-offloads/codex-pv-route2-20261027/dropfree');args=sys.argv[:];sys.argv=[args[0]];globals().update(runpy.run_path(str(D/'run.py')));sys.argv=args
roots={226:'public_bytes',250:'ordinary_sample',134:'active_row_masks',36:'array_try_from',205:'finalize_variable_core',212:'finalize',215:'finalize_into',216:'update',217:'new',219:'finalize_fixed_core'}
op=int(sys.argv[1]);suffix=os.environ.get('VARIANT','01');key=f'{op}-{suffix}';P=D/'packages'/key;P.mkdir(parents=True)
(P/'Cargo.toml').write_text((D/'packages/252-05/Cargo.toml').read_text());(P/'lib.rs').write_bytes((D/'probes'/os.environ.get('PROBE_SOURCE',f'{op}.rs')).read_bytes());llbc=D/f'PV_R2_DF_{op}_{suffix}.llbc';out=D/f'generated-{key}';out.mkdir()
charon=['timeout','180','env','PATH=/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','RUSTUP_TOOLCHAIN=nightly-2026-06-01','RUSTFLAGS=--cfg pv_cb_extract','CARGO_TARGET_DIR='+str(D.parent/'charon-target'),str(BASE/'charon'),'cargo','--preset','aeneas','--mir','optimized','--sysroot','default','--start-from','crate::'+roots[op],'--include','pv_r2_dropfree::*','--include','aspis_core::field::*','--dest-file',str(llbc),'--','--manifest-path',str(P/'Cargo.toml'),'--release','--offline','--lib','--jobs','4']
if os.environ.get('VEC_BODY')=='1':charon[charon.index('--dest-file'):charon.index('--dest-file')]=['--include','alloc::vec::*','--include','alloc::raw_vec::*']
aeneas=['timeout','180','/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools/aeneas','-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace',f'PV_R2_DF_{op}_{suffix}','-dest',str(out),'-split-files','-emit-json',str(llbc)]
packet=D/f'phase-input-{key}';packet.mkdir();rows=[dict(target=cmd,cwd=str(P),directory=str(D/(phase+'-'+key)),revision=REV,preflight=True,expected_time='optimized MIR compilation and symbolic extraction; no arithmetic elimination') for phase,cmd in [('charon',charon),('aeneas',aeneas)]];(packet/'phases.json').write_text(json.dumps(rows,indent=2))
if os.environ.get('PREPARE_ONLY')!='1':run('scope-'+key,['python3',str(D/'phases.py'),str(packet)],P)
