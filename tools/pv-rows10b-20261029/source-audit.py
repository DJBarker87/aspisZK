from pathlib import Path
import subprocess,json,hashlib,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rows10b-20261029';E.mkdir(exist_ok=True)
sha=lambda b:hashlib.sha256(b).hexdigest()
revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
files=['crates/aspis-prover/src/state_only_entropy.rs','crates/aspis-r1-cost-probe/src/host_sumcheck.rs','crates/aspis-prover/src/host_arithmetic.rs','crates/aspis-r1-cost-probe/src/r1_wire.rs','docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullExternalFuns.lean','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_TrustItems.lean','docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitPublicNonce40.lean','docs/research/v8-r0-zk-20261009/lean/R0Z/FsStatement.lean']
pins=[];contents={}
for f in files:
 b=subprocess.check_output(['git','show','HEAD:'+f]);contents[f]=b.decode()
 pins.append(dict(path=f,revision=revision,blob=subprocess.check_output(['git','rev-parse','HEAD:'+f],text=True).strip(),sha256=sha(b),bytes=len(b)))
 (E/'source').mkdir(exist_ok=True)
 (E/'source'/(Path(f).name+'.txt')).write_bytes(b)
old=R/'evidence/pv-rows10-20261029/getrandom-0.3.4'
# A statement inventory and model coordinates, NOT a complete own-1 certificate.
spec=[('src/backends/linux_android_with_fallback.rs.txt','GETRANDOM_FN.load(Ordering::Acquire)','PV_ROWS10B_Dispatch.Cache / dispatch'),('src/backends/linux_android_with_fallback.rs.txt','libc::dlsym(libc::RTLD_DEFAULT, name_ptr)','PV_ROWS10B_Link_SymbolOrigin (UNDISCHARGED)'),('src/backends/linux_android_with_fallback.rs.txt','getrandom_fn(dangling_ptr, 0, 0)','PV_ROWS10B_Dispatch.initChoice / Probe'),('src/backends/linux_android_with_fallback.rs.txt','GETRANDOM_FN.store(res_ptr.as_ptr(), Ordering::Release)','source store; no native World instance'),('src/backends/linux_android_with_fallback.rs.txt','util_libc::sys_fill_exact(dest','PV_ROWS10B_ControlWord.sysStep/run (control model only)'),('src/backends/use_file.rs.txt','FD.load(Ordering::Acquire)','PV_ROWS10B_ControlWord.fdEntry/fdLock'),('src/backends/use_file.rs.txt','FD.compare_exchange_weak(','Site.compareExchange (actual atomic effect not instantiated)'),('src/backends/use_file.rs.txt','FD.store(val, Ordering::Release)','PV_ROWS10B_ControlWord.fdPublish'),('src/backends/use_file.rs.txt','libc::read(fd, buf.as_mut_ptr().cast::<c_void>(), buf.len())','Site.read, sysStep/run'),('src/backends/use_file.rs.txt','open_readonly(FILE_PATH)?','Site.openUrandom, openStep'),('src/backends/use_file.rs.txt','open_readonly(b"/dev/random\\0")?','Site.openRandom, openStep'),('src/backends/use_file.rs.txt','libc::poll(&mut pfd, 1, -1)','Site.pollRandom, pollStep'),('src/backends/use_file.rs.txt','libc::close(fd)','Site.closeRandom'),('src/backends/use_file.rs.txt','libc::SYS_futex, &FD, op, FD_ONGOING_INIT, timeout_ptr','Site.futexWait (deployed debug checks disabled)'),('src/backends/use_file.rs.txt','libc::SYS_futex, &FD, op, libc::INT_MAX','Site.futexWake (deployed debug checks disabled)'),('src/util_libc.rs.txt','buf.get_mut(len..).ok_or(Error::UNEXPECTED)?','sysStep.advance; mutable slice frame still requires source link'),('src/util_libc.rs.txt','err.raw_os_error() != Some(libc::EINTR)','sysStep.retry/error'),('src/util_libc.rs.txt','Error::ERRNO_NOT_POSITIVE','lastError'),('src/lib.rs.txt','if !dest.is_empty()','PV_ROWS10B_Consumed.fill'),('src/lib.rs.txt','fill_uninit(unsafe { util::slice_as_uninit_mut(dest) })?','PV_ROWS10B_Consumed.fill')]
rows=[]
for f,needle,target in spec:
 b=(old/f).read_bytes();s=b.decode();assert needle in s,(f,needle)
 rows.append(dict(source=str((old/f).relative_to(R)),sha256=sha(b),needle=needle,line=s[:s.index(needle)].count('\n')+1,model_coordinate=target,evidence_class='checked source inventory; not full structural (K-1 substitute) binding'))
raw=contents[files[-1]];law=contents[files[-2]];trust=contents[files[-3]]
assert 'abbrev OracleAnswer := Fin 32 → UInt8' in raw
assert 'abbrev Raw := Fin 2 → OracleAnswer' in law
assert '∀ context raw, law context raw = 1 / (Fintype.card Raw : ℚ)' in law
assert 'entropy_law : ProverCommitPublicNonce40.E1 d.law' in trust
assert 'entropy_kernel : ∀ c, d.nativeWeight c =' in trust
assert 'PV_RunJoin_E1Joint.weight 128 d.law d.frame d.coordinates c' in trust
caller=contents[files[0]];start=caller.index('pub fn generate_for_mask_nonce(');end=caller.index('pub fn mask_nonce(',start);body=caller[start:end]
assert 'Zeroizing::new([0u8; 64])'in body and 'getrandom::fill(bytes.as_mut())?'in body
assert 'ENTROPY_RETRY_LIMIT'in body and 'entropy_nonzero32(&mask_nonce)'in body
j=dict(revision=revision,source_pins=pins,source_coordinates=rows,complete_own1_binding=False,exact_first_blocker='PV_ROWS10B_Link_SymbolOrigin: authorized dlsym target and cached callable identity in the actual admitted deployment',not_proved=['native pointer/FD atomic World interpretation','libc/dynamic-target-to-syscall refinement','actual complete control-word witness independence at the 64-byte caller','actual callback coordinates/native kernel association'],exact_T='unchanged; only E1 schema specialized to identical Raw; no imported TrustItems object and no native E1 or joint-kernel proof',caller64=dict(source=files[0],body_sha256=sha(body.encode()),request_bytes=64,no_failure_publicness_inference=True),V403=dict(source=files[1],call='evaluate_state_only_polynomial(&polynomial, point[round])',native_import='aspis_prover::host_arithmetic',selected_op121='aspis_core.state_only_sumcheck.evaluate_state_only_polynomial',status='native event/prefix association not supplied; not a finding of unreachable noncanonical data'))
(E/'source-audit.json').write_text(json.dumps(j,indent=2)+'\n')
print('checked',len(pins),'candidate source pins and',len(rows),'dependency source coordinates; full own-1 binding remains open')
