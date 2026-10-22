#!/usr/bin/env python3
"""Read-only integrity validation for the side-channel audit receipts."""
from pathlib import Path
import hashlib,json,resource,subprocess,sys,time
E=Path(__file__).resolve().parent;R=E.parents[4];start=time.monotonic()
manifest=json.loads((E/'source-inventory.json').read_text());base=manifest['source_baseline']
checks=[]
for pin in manifest['files']+manifest['configuration_pins']:
    p=pin['path'];raw=(R/p).read_bytes()
    old=subprocess.check_output(['git','show',base+':'+p],cwd=R)
    checks.append(dict(path=p,worktree_sha_matches=hashlib.sha256(raw).hexdigest()==pin['sha256'],baseline_sha_matches=hashlib.sha256(old).hexdigest()==pin['sha256'],size_matches=len(raw)==pin['bytes']))
anchors={
'crates/aspis-prover/src/state_only_entropy.rs':['pub fn generate_for_mask_nonce(', 'Zeroizing::new([0u8; 64])','if *field_mask_entropy != [0; 32] && *leaf_salt_seed != [0; 32]', 'file.write_all(RESERVATION_MAGIC)?;','file.write_all(&statement_digest)?;','file.write_all(&mask_nonce)?;'],
'crates/aspis-r1-cost-probe/src/prover.rs':['pub const ATTEMPT_CAP: usize = 8;', 'Err(Error::Rejected)=>continue,','CHECK_TIMES.with(|v| v.borrow_mut().push(times));','StateOnlyAttemptSecrets::generate().map_err(|_|Error::Entropy)'],
'crates/aspis-r1-cost-probe/src/host_semantic.rs':['clear &= chi != *value;', 'if !no_pole(compiled, lambda, chi)? {','let values = lean_copy_row_values(&compiled.trace, lambda)?;'],
'crates/aspis-core/src/field.rs':['M31(if s >= P { s - P } else { s })','if self.0 == 0 {','assert!(self.0 != 0, "inverse of zero");'],
'crates/aspis-statement/src/constraints_v4.rs':['fn sparse_eq_weights(','.take_while(|value| **value == QM31::ZERO || **value == QM31::ONE)','Vec::with_capacity(1usize << prefix_len)'],
'crates/aspis-r1-cost-probe/src/trace.rs':['#[cfg(feature="prover")]','VALUES.with(|v| v.borrow_mut().push((tag,index,x.to_le_bytes())));'],
'docs/research/v8-r0-zk-20261009/z4/z9e.rs':['pub fn p_r1_check(ch: &R1PublicChallenges)', 'std::panic::catch_unwind','tm.emit = t.elapsed().as_secs_f64();'],
'crates/aspis-r1-cost-probe/src/sim.rs':['t.0.insert(concat(parts),self.answer)', 'folded.entry(v).or_insert_with', 'let parents:BTreeSet<usize>'],
'tools/r1-cost-probe/src/bin/devnet_spend/plan.rs':['let result=prover::prove_masked_retrying(', 'open(dir.join("note-recovery.json"))?', 'fs::write(dir.join("proof.bin"),&proof)?;'],
'scripts/r1_devnet_spend.py':['with ThreadPoolExecutor(max_workers=4)', 'body[start:start+3763]', "time.sleep((i%4)*.25)"]}
anchor_results=[]
for p,needles in anchors.items():
    src=(R/p).read_text()
    for needle in needles:
        ok=needle in src
        anchor_results.append(dict(path=p,anchor=needle,found=ok,line=src[:src.index(needle)].count('\n')+1 if ok else None))
# This worktree started clean; only this report/evidence tree may differ from the task baseline.
changed=subprocess.check_output(['git','diff','--name-only',base],cwd=R,text=True).splitlines()
status=subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],cwd=R,text=True).splitlines()
allowed_prefix='docs/research/100bit-spend-path-20261013/evidence/sidechannel-20261022/'
report='docs/research/v8-r0-zk-20261009/r1p-final/SIDE-CHANNEL-AUDIT-20261022.md'
all_paths=set(changed)|{x[3:] for x in status}
allowed=all(x==report or x.startswith(allowed_prefix) for x in all_paths)
ws=subprocess.run(['git','diff','--check',base],cwd=R,capture_output=True,text=True)
result_checks=json.loads((E/'checks.json').read_text())
passed=all(all(c[k] for k in ('worktree_sha_matches','baseline_sha_matches','size_matches')) for c in checks) and all(c['found'] for c in anchor_results) and allowed and ws.returncode==0 and result_checks['exit']==0
usage=resource.getrusage(resource.RUSAGE_SELF)
out=dict(command='python3 '+allowed_prefix+'validate.py',validation_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),baseline=base,exit=0 if passed else 1,wall_seconds=time.monotonic()-start,peak_rss_kib=usage.ru_maxrss//1024 if sys.platform=='darwin' else usage.ru_maxrss,swaps=usage.ru_nswap,axioms='not applicable: no Lean attempt',source_pins=checks,source_anchors=anchor_results,allowed_file_policy=allowed,changed_paths=sorted(all_paths),whitespace_check=dict(command='git diff --check '+base,exit=ws.returncode,output=ws.stdout+ws.stderr),tiny_checks_exit=result_checks['exit'],frozen_elf_rebuild='not triggered: no crate/program source edits; not run',native_or_hardware_evidence='none; no new timing, disassembly, Kani or Lean result')
(E/'validation.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(exit=out['exit'],source_pins=len(checks),anchors=len(anchor_results),allowed_file_policy=allowed,wall_seconds=out['wall_seconds'])))
sys.exit(out['exit'])
