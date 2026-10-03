import ast,pathlib,json,hashlib
W=pathlib.Path.cwd(); H=W/'.r21-scratch/r428-slice-next-source-capture/root-launch'
p=W/'.r21-scratch/r427-raw-mir-observation-preflight/launch-gated-runner-attempt-c/launch_r427.py'
t=ast.parse(p.read_text()); remote=None
for n in ast.walk(t):
 if isinstance(n,ast.Assign) and any(isinstance(v,ast.Name) and v.id=='remote' for v in n.targets) and isinstance(n.value,ast.Constant) and isinstance(n.value.value,str) and 'effective_cgroup' in n.value.value: remote=n.value.value
assert remote
base=W/'.r21-scratch/r428-slice-next-source-capture/base-r327/extract-command.json'
assert hashlib.sha256(base.read_bytes()).hexdigest()=='021c55ed604170e5982365f714d4abd46edf4b14ad0d626b1c59d25f8b6da1ad'
plan=json.loads(base.read_text()); assert plan['monomorphize'] is True
assert plan['start_from']==['crate::circle_norm::joined_inverse::line_norm::r110_norm::batch']
assert hashlib.sha256(json.dumps(plan['rustflags'],separators=(',',':')).encode()).hexdigest()==plan['rustflags_sha256']
# Remove diagnostic-overlay-only inputs; retain the original toolchain pin and reservation gates.
remote='\n'.join(x for x in remote.splitlines() if not any(s in x for s in ["candidate=pathlib.Path", "assert sha(candidate/", "preserved-original-binaries", "shutil.copy2(original", "os.environ['ASPIS_R427_OBSERVE_MIR']", '# Raw observer']))+'\n'
remote=remote.replace("'aspis-r427-raw-mir-capture.service'", "'aspis-r428-slice-next-source.service'")
remote=remote.replace("command += ['--dest-file'", "command += ['--monomorphize','--dest-file'")
remote=remote.replace('R427RawMirCapture.llbc','R428SliceNextSource.llbc').replace("'monomorphize':False,'environment':{'ASPIS_R427_OBSERVE_MIR':'1'}", "'monomorphize':True,'environment':{}")
remote=remote.replace('R427_CHILD_EXIT','R428_CHILD_EXIT').replace('R396 baseline','R327 baseline')
# Original source must remain at its pinned Git revision, with no tracked changes.
needle='assert not root.exists(),f"capture root already exists: {root}"'
remote=remote.replace(needle,'''charon_source=pathlib.Path('/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon')
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=charon_source,text=True).strip()=='cb50ff16b9f1066b8a97dc06da704de2da2fa41c'
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=charon_source,text=True).strip()
assert sha(charon_source/'charon/Cargo.lock')=='c755a326679e9b3dbce560ff15130bdc83ae16178f2c1af568e391b8470d2e67'
'''+needle)
# Derive the exact argv from the immutable complete base, changing only include scope and destination.
start=remote.index("command=[str(wrapper),'cargo'"); end=remote.index("assert '--print-original-ullbc'",start)
cmd=plan['command'].copy(); i=cmd.index('--monomorphize'); cmd[i:i]=['--include','core::slice::iter::_::next']; cmd[cmd.index('--dest-file')+1]='/home/dombarker/project-offloads/aspis-r428-slice-next-source-20261003-a/R428SliceNextSource.llbc'
remote=remote[:start]+'command='+repr(cmd)+'\n'+remote[end:]
# Recheck original toolchain binaries after extraction as well.
remote=remote.replace('assert source_after==expected,source_after', '''assert source_after==expected,source_after
assert sha(wrapper)=='@WRAPPER_SHA@' and sha(driver)=='@DRIVER_SHA@'
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=charon_source,text=True).strip()''')
repl={'@SOURCE_ROOT@':'/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a','@CAPTURE_ROOT@':'/home/dombarker/project-offloads/aspis-r428-slice-next-source-20261003-a','@WRAPPER@':cmd[0],'@DRIVER@':cmd[0]+'-driver','@ORIGINAL_WRAPPER@':cmd[0],'@ORIGINAL_DRIVER@':cmd[0]+'-driver','@REMOTE_BASELINE@':'/home/dombarker/project-offloads/aspis-r327-private-batch-source-try-fold-20261002-a/R327PrivateBatchSourceTryFold.llbc','@RUSTC@':'/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/bin/rustc','@BASELINE_SHA@':'9ed7c0ab91051ac61d812d66651680112ac26fe907faa76f9d4d2d9a14d03442','@WRAPPER_SHA@':'b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c','@DRIVER_SHA@':'4cb603ad51132f298a63a9c2a8cc8c629c73edeff22516fbf56ba5decee70938','@ORIGINAL_DRIVER_SHA@':'4cb603ad51132f298a63a9c2a8cc8c629c73edeff22516fbf56ba5decee70938','@RUSTC_COMMIT@':'14210df0e27ccd7d9e6a05b8085cbd438e4bbc65','@EXPECTED_RUSTFLAGS@':repr(plan['rustflags']),'@RUSTFLAGS_SHA@':plan['rustflags_sha256'],'@ROOT@':repr(plan['start_from'][0]),'@ROOTS@':repr(plan['start_from']),'@INCLUDES@':repr(plan['include']+['core::slice::iter::_::next']),'@RECEIPT_SHA@':hashlib.sha256(base.read_bytes()).hexdigest(),'@LAUNCH_REV@':'09b9bef079186b1b34354c4c5519b79d3a8ff096','@GET_MIR_SHA@':'N/A original driver; no observation hook','@PATCH_SHA@':'N/A original source untouched','@SOURCE_COMMIT@':'cb50ff16b9f1066b8a97dc06da704de2da2fa41c'}
for k,v in repl.items(): remote=remote.replace(k,v)
assert '@' not in remote
remote=remote.replace("'source_revision_recorded':'13617a70553ed3c43cee312acba2407b29a7052d'", "'source_revision_recorded':'d4bf07b08443136de0a11fc1fd932bd604586c2e'")
remote=remote.replace("'reviewed_build_receipt_sha256'", "'base_extract_command_sha256'").replace('candidate_driver_sha256','original_driver_sha256')
import textwrap
remote="import pathlib,json,traceback\ntry:\n"+textwrap.indent(remote,'    ')+'''\nexcept BaseException as exc:
    if 'root' in globals() and not root_preexisting:
        root.mkdir(parents=True,exist_ok=True)
        (root/'runner-status.json').write_text(json.dumps({'status':'terminal','code':getattr(exc,'code',None),'failure':repr(exc),'traceback':traceback.format_exc(),'effective_cgroup':globals().get('effective_before')},indent=2))
    raise
'''
ast.parse(remote)
(H/'remote.py').write_text(remote)
(H/'planned-command.json').write_text(json.dumps({'base_plan_sha256':hashlib.sha256(base.read_bytes()).hexdigest(),'command':cmd,'only_scope_delta':['--include','core::slice::iter::_::next'],'monomorphize':True,'formal_axioms':'N/A extraction, no Lean theorem'},indent=2)+'\n')
print('PREPARED',hashlib.sha256(remote.encode()).hexdigest())
