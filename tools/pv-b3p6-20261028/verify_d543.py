"""Fail-closed receipt, source, budget and local coverage reconciliation."""
from pathlib import Path
import hashlib,json,re,subprocess
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';L=D/'lean';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inv=json.loads((R/'D543-final-host-inventory.json').read_text());bad=[]
for name,h in inv['hashes'].items():
 p=R/name.removeprefix('resume18/')
 if not p.is_file()or sha(p)!=h:bad.append(name)
assert not bad,bad
assert '0 loaded units listed'in inv['scopes']
assert inv['lean_attempts']==10 and inv['extraction_receipts']==2 and inv['kani_receipts']==2
lean=[];seen=set();failed={}
for p in sorted(R.glob('lean-790*/receipt/receipt.json')):
 r=json.loads(p.read_text());assert r['attempt']not in seen;seen.add(r['attempt'])
 assert r['source_sha256']==sha(p.parent.parent/'source.lean')
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}and r['swaps']==0
 authority=r['project_source_authority'];blob=subprocess.check_output(['git','cat-file','blob',authority['blob']]);assert hashlib.sha256(blob).hexdigest()==authority['sha256']==r['source_sha256']
 if r['exit_status']==0:
  assert r['source_sha256']not in failed,(r['attempt'],failed)
  log=(p.parent/'stdout.log').read_text();assert 'sorryAx'not in log and 'error:'not in log
  ax=re.findall(r'depends on axioms: \[([^\]]*)\]',log)
  assert ax or 'does not depend on any axioms'in log
  assert all(set(a.replace('\n','').replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}for a in ax)
  assert sha(L/(r['module']+'.lean'))==r['source_sha256']
 else:failed[r['source_sha256']]=r['attempt']
 lean.append({k:r[k]for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','lean_source_revision','source_sha256','print_axioms']})
assert seen==set(range(79000,79009))|{79097}
audit=next(r for r in lean if r['attempt']==79097);assert audit['exit_status']==0
log=(R/'lean-79097/receipt/stdout.log').read_text();assert log.count('depends on axioms:')+log.count('does not depend on any axioms')==21
native=[]
for kind,ids in [('N',[79160,79161]),('K',[79100,79101])]:
 for i in ids:
  p=R/f'{kind}{i}/receipt/receipt.json';r=json.loads(p.read_text())
  assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}and r['swaps']==0
  if kind=='N':assert r['exit_status']==0
  native.append(dict(id=f'{kind}{i}',**{k:r[k]for k in ['exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','print_axioms']}))
control=(R/'K79100/receipt/stdout.log').read_text();positive=(R/'K79101/receipt/stdout.log').read_text()
assert 'Failed Checks: assertion failed: left == right'in control
assert 'equivalence18::raw_all_words_wrong'in control
assert 'VERIFICATION:- FAILED'in positive and 'Failed Checks: attempt to subtract with overflow'in positive
assert 'Failed Checks: assertion failed: left == right'not in positive
# The new full-domain pair is failure evidence only; never positive credit.
assert next(n for n in native if n['id']=='K79101')['exit_status']==1
for n in ['compile_resume18.py','preflight_resume18_host.py','kani543_host.py','kani_inner227_resume18_host.py','reference_extract543_host.py','scan_ids_d543_host.py']:
 assert sha(R/n)==sha(Path('tools/pv-b3p6-20261028')/n)
for p in R.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20*1024*1024,p
# No deployed Rust, release artifact, endpoint/soundness or unrelated file edit.
changed=subprocess.check_output(['git','diff','--name-only','a64f41b1e5..HEAD'],text=True).splitlines()
assert not any(p.startswith(('crates/','programs/','design/'))for p in changed)
t=json.loads((R/'TALLY-resume18.json').read_text());assert t['lean_attempts']==10 and t['used_ids']==list(range(79000,79009))+[79097]
old=json.loads((D/'resume17/PER-FUNCTION-D542.json').read_text());rows=[]
new={'validate_transition':('Kani (k-triple-prime)','transition_reference_link543','TRANSITION-SOURCE-D543.json'),
 'equality_value':('Lean equality + own-1 structural','equality_source_link543','LOCAL-SOURCE-BINDINGS-D543.json'),
 'occupancy_lanes_literal':('Lean equality + own-1 structural','occupancy_source_link543','LOCAL-SOURCE-BINDINGS-D543.json'),
 'poseidon_selectors':('Lean equality + own-1 structural','poseidon_selectors_source_link543','LOCAL-SOURCE-BINDINGS-D543.json'),
 'interpolate_three_constant_columns':('Lean equality + own-1 structural','interpolation_source_link543','LOCAL-SOURCE-BINDINGS-D543.json'),
 'internal_linear_lazy':('Lean equality + own-1 structural, total wrapping domain','internal_source_link543','INTERNAL-SOURCE-D543.json')}
for r in old['functions']:
 key=(r['family'],r['function']);bound=False;route='OPEN';theorem=r.get('theorem');evidence='resume17/PER-FUNCTION-D542.json'
 if r['direct']['status']=='EXTRACTED':bound=True;route='direct extraction'
 elif r['function']=='reconstruct_10':bound=True;route='Kani (k-double-prime)'
 elif r['function']=='sum_high':bound=True;route='Lean equality + own-1 structural'
 elif r['function']in new:
  bound=True;route,theorem,evidence=new[r['function']]
 rows.append(dict(family=r['family'],function=r['function'],direct_status=r['direct']['status'],verbatim_refusal_record='resume17/PER-FUNCTION-D542.json / original receipts'if r['direct']['status']!='EXTRACTED'else None,local_body_association='BOUND'if bound else'OPEN',route=route,theorem=theorem,evidence=evidence,remaining=('Whole std/D188/matrix/callback and V370 retained; no endpoint closure'if bound else r.get('residual'))))
assert len(rows)==36 and sum(r['local_body_association']=='BOUND'for r in rows)==12
counts=dict(total=36,bound=12,open=24,direct_extraction=4,Kani=2,Lean_equality_with_structural_source_binding=6)
coverage=dict(target='V244 / runjoin op227 OPEN; target not established',counts=counts,functions=rows,new_associations=list(new),scope='Local body associations only, same counting convention as resume17; full native source-cone closure and endpoint premises remain open',route_labels=dict(Kani_reconstruct="P6, strict std parity k'', compiler cohort V370",Kani_transition="Kani equivalence (P6) with std parity by token identity plus structural per-item arguments (k''')",Lean='Structural source argument plus compiled complete-Result equality, not machine proof; compiler/runtime V370 retained'))
(R/'PER-FUNCTION-D543.json').write_text(json.dumps(coverage,indent=2)+'\n')
manifest={p.name:sha(p)for p in L.glob('PV_B3P_*543227.lean')}
(R/'FOCUSED-MANIFEST-D543.json').write_text(json.dumps(dict(modules=manifest,audit=79097,scope='One changed focused source-link import closure, not a complete endpoint release replay',axioms_prints=21),indent=2)+'\n')
out=dict(target=coverage['target'],entry_revision='a64f41b1e55d360c3d41ea0928669b0007909b5f',branch=subprocess.check_output(['git','branch','--show-current'],text=True).strip(),host_artifacts_verified=len(inv['hashes']),mismatches=bad,lean=lean,native=native,coverage=counts,budget=dict(charged=dict(lean=10,extraction=2,kani=2),remaining=dict(lean=70,extraction=28,kani=28),next=dict(lean=79009,audit=[79098,79099],extraction='N79162',kani='K79104 after fresh collision scan'),retired_unlaunched=['K79102','K79103'],notes='Two prepared internal all-word gates were not launched; do not spend runs repeating the known checked-MIR boundary. Old resume17 leftovers are retired.'),accepted_new_source_dossiers=['TRANSITION-SOURCE-D543.json','LOCAL-SOURCE-BINDINGS-D543.json','INTERNAL-SOURCE-D543.json'],failed_proof_attempts=[79001,79004,79005],failures='Reserved binder public at79001; explicit usize-size witness/type normalization at79004/05. All replacements changed source, failed receipts retained and earn no credit.',Kani='K79100 intended XOR-assertion FAIL (also overflow checks); K79101 FAILED only checked-MIR subtraction conditions. No new Kani positive credit. Historical static-free K72135/reconstruct transfers retained; suspended K-3 rows remain suspended.',axioms='21 declarations in final audit; only propext, Classical.choice, Quot.sound',premise_changes=dict(removed=[],added=[],weakened=[]),resources='one scope at a time;6G/8G/swap0/Tasks64;Lean-M7000; optimized Rust/Kani, no raised limits',source_revisions='Exact Lean revisions/blobs per h5 receipt; legacy Rust revision labels are retained verbatim and supplemented by frozen file hashes in scope inputs. No deployed Rust changed.',full_release_replay='Not run: actual whole-callback and complete source-cone obligations remain open; no unchanged full regression repeated',live_scopes=inv['scopes'])
(R/'verification-summary-D543.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(host_hashes_verified=len(inv['hashes']),lean=10,extraction=2,kani=2,coverage=counts,audit=79097,axioms=21)))
