from pathlib import Path
import json,hashlib,re,lzma
D=Path('/home/dombarker/project-offloads/codex-pv-diag9-20261029');S=D.parent/'codex-pv-fscan-20261028/src';P=D.parent/'codex-pv-diag-20261029';E=D.parent/'codex-pv-diag8-20261029'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((P/'source-identity.json').read_text())['checks']
for r in pins:assert sha(S/r['path'])==r['sha256'],r['path']
rows=[]
for rel in ['tools/r1-cost-probe/src/bin/devnet_spend/plan.rs','tools/r1-cost-probe/src/bin/devnet_spend.rs','tools/r1-cost-probe/src/bin/devnet_spend/Client64_accounts.rs']:
 p=S/rel;s=p.read_text()
 for line,t in enumerate(s.splitlines(),1):
  kinds=[k for k in ['.map_err(err)','format!','println!','eprintln!','ensure!','anyhow!'] if k in t]
  if kinds:rows.append(dict(path=rel,line=line,source=t.strip(),kinds=kinds,file_sha256=sha(p),status='selected content/operands only; occurrence and delivery require original joint L1/option-B/native binding'))
plan=(S/'tools/r1-cost-probe/src/bin/devnet_spend/plan.rs').read_text()
assert 'fn err(e:impl std::fmt::Debug)->anyhow::Error{anyhow!("{e:?}")}' in plan
assert 'let result=RealR1_client::prove_for_proof_accounts(' in plan
assert '|k| accounts.nonce(k)).map_err(err)?;' in plan
# Normal return reaches this map_err; called prover frames are popped. Every
# earlier effect, panic-hook entry and pre-existing captured backtrace stays retained.
normal=dict(site='plan.rs:122 -> plan.rs:21',steps=['RealR1_client::prove_for_proof_accounts completes a NORMAL Rust Result return','Result::map_err invokes err only for Err; the original prover call has returned','err formats the Debug value into anyhow! construction','selected capture is in formatter/constructor at this fixed caller site; normal returned prover frames are no longer live'],laws=['normal_return_restores','selected_capture_public_after_return','returned_error_callsite_frames','complete_capture_transport'],retained=['public joint error variant/site occurrence','no earlier capture/log/hook effect has been erased','formatter/anyhow constructor call cone, unwinder PC correspondence, inlining and build/module/resolver state','allocation failure/hook/unwind/OOM branches','V370 pending D381/D386'])
# Inspect the complete verifier error declaration (unit variants), not panic messages.
rel='crates/aspis-verifier/src/lib.rs'
# Find the actual verifier declaration in the frozen source tree.
errs=[]
for pin in pins:
 rel=pin['path'];p=S/rel
 if p.suffix!='.rs':continue
 if 'verifier' not in rel:continue
 s=p.read_text()
 for m in re.finditer(r'pub enum Error\s*\{([^}]+)\}',s,re.S):
  text=re.sub(r'//[^\n]*','',m[1]); attributes=re.findall(r'#\[[^]]*\]',text)
  assert all(a=='#[cfg(feature="prover")]' for a in attributes),(rel,attributes)
  text=re.sub(r'#\[[^]]*\]','',text);variants=[x.strip() for x in text.split(',') if x.strip()]
  errs.append(dict(path=rel,file_sha256=sha(p),line=s[:m.start()].count('\n')+1,variants=variants,unit_only=all(re.fullmatch(r'[A-Za-z_]\w*',v) for v in variants)))
assert any(r['unit_only'] and 'AttemptsExhausted' in r['variants'] and 'Entropy' in r['variants'] for r in errs)
trace=S/'crates/aspis-statement/src/pool_v1/pair_trace.rs';t=trace.read_text();assert 'BlockMismatch { block: u8, local_row: u8, lane: u8 }' in t;assert 'AuxiliaryMismatch { row: u16, column: u8 }' in t
# These are dynamic operands and MUST NOT be relabelled environmental.
traceErrors=dict(path=str(trace.relative_to(S)),sha256=sha(trace),sites=['BlockMismatch { block:u8, local_row:u8, lane:u8 }','AuxiliaryMismatch { row:u16, column:u8 }'],status='numeric mismatch coordinates are dynamic; compiler call errors excluded only on the successful canonical-preparation call. No blanket public Debug law for arbitrary error values.')
z=S/'docs/research/v8-r0-zk-20261009/z4/z9e.rs';t=z.read_text();start=t.index('pub fn p_r1_check');body=t[start:]
assert 'std::panic::catch_unwind' in body and 'matches!(verdict, Ok(Some(true)))' in body
check=dict(path=str(z.relative_to(S)),sha256=sha(z),span=[196,220],calls=['public_data(ch)','emit(&p)','Lanes::new(&p.cx)','convert(&p,&cert,&ln)','extracted_builders(&p,&cert,&ln,&mut pb)','ck::check(&pb,&cc)'],gap='no complete honest Result law for this reached native cone; a normal catch_unwind wrapper return alone cannot exclude an internally caught panic',suppression_is_not_exclusion=True)
logger=json.loads((E/'logger-reachability.json').read_text());logs=json.loads((E/'logger-ir-sites.json').read_text())
report=dict(pinned_source_inputs_checked=len(pins),source_pin_manifest_sha256=sha(P/'source-identity.json'),sites=rows,normal_return_capture=normal,verifier_error_enums=errs,compiler_dynamic_errors=traceErrors,checker_uncovered=check,logger=dict(candidate_count=len(logs),inventory_sha256=sha(E/'logger-ir-sites.json'),reachability_sha256=sha(E/'logger-reachability.json'),named_targets=logger['targets'],complete_honest_reachability=False,remaining='inlined/indirect callbacks and actual operands/global-state law; config is only one component'),compiler_boundary='V370 / D381 / D386',new_trust=0,complete_native_diagnostic_law=False)
(D/'source-bindings.json').write_text(json.dumps(report,indent=2)+'\n')
# Exact unchanged conservative candidates inherited by hash, not copied or promoted.
(D/'inherited-inventory-pins.json').write_text(json.dumps({f:dict(path=str(E/f),sha256=sha(E/f)) for f in ['source-site-inventory.json.xz','selected-ir-sites.json','logger-ir-sites.json','logger-reachability.json','audit-source-binding.json','source-bindings.json']},indent=2)+'\n')
print('source pins',len(pins),'dynamic/literal sites',len(rows),'logger candidates',len(logs),'normal-return capture boundary bound; whole cones remain open')
