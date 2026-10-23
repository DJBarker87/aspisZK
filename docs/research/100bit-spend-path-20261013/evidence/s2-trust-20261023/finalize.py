import pathlib,json,re,hashlib,subprocess,difflib
p=pathlib.Path(__file__).resolve().parent
root=p.parents[4];lean=p.parents[1]/'lean'
def sha(t): return hashlib.sha256(t).hexdigest()
def load(f): return json.loads(f.read_text())
receipts=[load(f) for f in sorted(p.glob('lean-*/receipt.json'))+sorted(p.glob('kani-*/receipt.json'))]
assert len([r for r in receipts if r['kind']=='lean'])<=100
# Charge each requested harness, including compile failures and unstarted tails.
kani_charge=sum(max(1,r['command'].count('--harness')) for r in receipts if r['kind']=='kani')
assert kani_charge<=60
for r in receipts:
 note=p/r['attempt']/'measurement-note.json'
 if note.exists():
  r['time_reported_peak_rss_kib']=r['peak_rss_kib'];r['peak_rss_kib']=None;r['measurement_note']=load(note)
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['swaps']=='0'
for module,attempt in [('S2TrustedSdkBorrow.lean','lean-003'),('S2TrustConsistency.lean','lean-006')]:
 r=load(p/attempt/'receipt.json');assert r['exit_status']==0
 assert r['source_hashes'][module]==sha((lean/module).read_bytes())
 assert all('sorryAx' not in line for line in r['print_axioms'])
 for line in r['print_axioms']:
  m=re.search(r'depends on axioms: \[(.*)\]',line)
  if m: assert set(m[1].split(', '))<= {'propext','Classical.choice','Quot.sound'}
checked={}
for r in receipts:
 if r['kind']!='kani':continue
 text=(p/r['attempt']/'stdout.log').read_text()
 for m in re.finditer(r'Checking harness ([\w:]+)\.\.\.(.*?)(?=Checking harness |Manual Harness Summary:|\Z)',text,re.S):
  if 'VERIFICATION:- SUCCESSFUL' in m[2]:checked[m[1]]={'attempt':r['attempt'],'verification_seconds':re.search(r'Verification Time: ([0-9.]+)s',m[2])[1]}
fields='account_data_cell cell_payload cell_counter shared_ok shared_err exclusive_ok exclusive_err shared_deref exclusive_deref guard_move shared_drop exclusive_drop error_move_drop borrow_frame guard_liveness'.split()
assert set('checks::'+n for n in fields+['step_contract','verified_stub_schedule'])<=set(checked),set(fields)-set(n.split('::')[-1] for n in checked)
for info in checked.values():
 r=next(r for r in receipts if r['attempt']==info['attempt'])
 assert r['exit_status']==0 and r['peak_rss_kib'] is not None, (info,r['exit_status'])
 info['wall_seconds']=r['wall_seconds'];info['peak_rss_kib']=r['peak_rss_kib'];info['swaps']=r['swaps']
v2=(p/'source/s2-spec-v2.rs').read_text();final=(p/'kani-spec/src/lib.rs').read_text()
assert v2.split('#[cfg(kani)]\nmod checks')[0]==final.split('#[cfg(kani)]\nmod checks')[0]
# The only final-source change is one extra admission condition in the consumer
# harness. Contract, all fifteen property harnesses, and every callee are identical.
assert v2.replace('s.guards[0].is_none() && vacant(&s,100)', 's.guards[0].is_none() && s.guards[1].is_none() && vacant(&s,100)')==final
(p/'rust-harness-delta.diff').write_text(''.join(difflib.unified_diff(v2.splitlines(True),final.splitlines(True),fromfile='source/s2-spec-v2.rs',tofile='kani-spec/src/lib.rs')))
manifest={'schema':'focused-extractor-proof-packet-v1','branch':'codex/cx-s2-trust-20261023','base_revision':'0998f05ffa0256157a35b270d4097a096fa17748','source_revision_at_collection':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),'exact_claim':'Universal mathematical consistency of the fifteen-field trust record; bounded Rust primitive spec contract, fifteen property checks and a verified-stub consumer schedule. NOT SDK certification or S2 caller closure.','assumptions_discharged':['joint satisfiability/non-vacuity of the specified mathematical interface'],'assumptions_retained':['approved SDK trust interpretation','production related-state admission','P6 toolchain/source/runtime correspondence','all common execution/caller/Required14/history/child-effect/binary obligations'],'assumptions_added':'none beyond the explicitly approved route B; bounded Rust domain recorded in AUDIT.md','budget':{'lean_attempts':sum(r['kind']=='lean' for r in receipts),'lean_limit':100,'kani_command_invocations':sum(r['kind']=='kani' for r in receipts),'kani_conservative_charge':kani_charge,'kani_limit':60},'accepted_lean':['lean-003','lean-006'],'accepted_kani':sorted(set(i['attempt'] for i in checked.values())),'checked_kani_harnesses':checked,'attempts':receipts,'tool_pins':load(p/'tool-pins.json'),'rust_primitive_closure_sha256':sha(final.split('#[cfg(kani)]\nmod checks')[0].encode()),'final_lean_sha256':{f:sha((lean/f).read_bytes()) for f in ['S2TrustedSdkBorrow.lean','S2TrustConsistency.lean']},'reuse':['S10 adopted ELF rebuilds (no shipped-file change; no new ELF build)','Lean pinned Std cache; no project aggregate replay','unchanged Rust primitive/contract/15-check declarations in v2 and final source (explicit delta retained)'],'remaining_blocker':'Production Library instance and initial typed relation; unchanged-caller simulation and common execution certificate are not supplied. Larger Rust capacity instantiations require their own checks.'}
(p/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'budget':manifest['budget'],'checked_harnesses':len(checked),'accepted_lean':manifest['accepted_lean']},indent=2))
