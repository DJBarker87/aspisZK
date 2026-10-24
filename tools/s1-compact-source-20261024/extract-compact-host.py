#!/usr/bin/env python3
"""Focused unchanged compact expansion extraction; own output/cache only."""
from pathlib import Path
import os,sys,subprocess,json,hashlib
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
phase=sys.argv[1];assert phase in ['charon','aeneas'];kind=sys.argv[2] if len(sys.argv)>2 else 'all';assert kind in ['all','semantic']
W=H/('s1-compact-native-v1-20261024' if kind=='all' else 's1-compact-semantic-native-v1-20261024')
P=Path('/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src')
T=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release')
A=Path('/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if phase=='charon':W.mkdir(exist_ok=False)
else:assert not json.loads((W/'Compact.llbc').read_text())['has_errors']
expected=json.loads((H/'kit/s1-compact-native-source-pins.json').read_text())
assert sha(P/'crates/aspis-r1-cost-probe/src/compact.rs')==expected['compact_sha256'],'compact source differs from current research'
# Wire contains unrelated later feature-gated additions. Pin this exact body,
# not a false complete-wire equality claim.
raw=(P/'crates/aspis-r1-cost-probe/src/r1_wire.rs').read_text();anchor='pub const fn row_shape(';start=raw.index(anchor);at=raw.index('{',start);depth=1;end=at+1
while depth:
 depth+=(raw[end]=='{')-(raw[end]=='}');end+=1
assert hashlib.sha256(raw[start:end].encode()).hexdigest()==expected['row_shape_sha256']
subprocess.run(['python3',str(H/'kit/reservation.py'),str(W/(phase+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
snap=subprocess.check_output(['python3','/home/dombarker/project-offloads/r1-circle-sample-wrapper-extraction-v2/collect-cgroups.py'],text=True)
(W/(phase+'-global-admission.json')).write_text(snap);admission=json.loads(snap);G=2**30
assert admission['effective_sum_bytes']+8*G<=48*G and admission['MemAvailable_kB']*1024>=14*G,'fresh global admission refused'
roots=['crate::compact::expand_values','crate::compact::expand_semantic','crate::compact::compact_row','crate::r1_wire::row_shape']
if kind=='semantic':roots.remove('crate::compact::expand_values')
constants=['crate::compact::SEMANTIC_ROWS','crate::compact::LOGICAL_SEMANTIC','crate::compact::SEMANTIC_COMPACT_VALUES','crate::compact::COMPACT_SEMANTIC','crate::verifier::SEMANTIC_BYTES','crate::r1_wire::CLAIMS','crate::r1_wire::LANES']
if phase=='charon':
 cmd=[str(T/'charon'),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','crate','--opaque','aspis_core','--opaque','aspis_statement']
 for n in roots+constants:cmd+=['--start-from',n,'--include',n]
 for n in ['core::option::Option','core::result::Result','crate::compact::CodecError']:cmd+=['--include',n]
 cmd+=['--dest-file',str(W/'Compact.llbc'),'--','--manifest-path',str(P/'crates/aspis-r1-cost-probe/Cargo.toml'),'--locked','--offline','--release','--lib','--features','optimized-terminal,program-build','--jobs','1']
else:
 cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-print-error-emitters','-loops-no-rec','-backend','lean','-namespace','AspisS1NativeCompact','-dest',str(W/'generated'),'-subdir','AspisS1NativeCompact','-split-files','-emit-json',str(W/'Compact.llbc')]
os.environ.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(H/'owned-charon-target'),CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
for n in ['RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH']:os.environ.pop(n,None)
meta=dict(schema='focused-extractor-proof-packet-v1',command=cmd,roots=roots,constants=constants,source_pins=expected,source_workspace=str(P),source_workspace_readonly=True,tools={str(p):sha(p) for p in [T/'charon',T/'charon-driver',A]},runner_sha256=sha(Path(__file__)),llbc_sha256=sha(W/'Compact.llbc') if phase=='aeneas' else None,qualification='Extraction feasibility for unchanged native helpers only; not whole-source/caller correspondence or native adoption.',expected_time='Cached optimized Rust compilation/source extraction, then focused Aeneas translation; no arithmetic/proof generation or elimination.')
(W/(phase+'-input.json')).write_text(json.dumps(meta,indent=2)+'\n')
os.chdir(W)
raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(W/(phase+'-receipt')),'Focused unchanged compact source extraction: cached optimized compilation, not arithmetic evaluation','--','timeout','180',*cmd]))
