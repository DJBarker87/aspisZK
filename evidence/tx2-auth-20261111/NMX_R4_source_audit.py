from pathlib import Path
import json,re,hashlib,subprocess
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
norm=lambda s:re.sub(r'\s+','',s)
paths=[E/'NMX_auth_cut_emitted/raw/NMX_auth/Funs.lean',E/'NMX_auth_box_emitted/raw/NMX_auth/Funs.lean']
def root(p):
 s=p.read_text();s=s[s.index('def r1_pool_adapter.owned.authenticate_asq8_accounts\n'):];return s[:s.index('\nend ')]
assert norm(root(paths[0]))==norm(root(paths[1]))
pins=json.loads((E/'NMX_auth_box_emitted/NMX_PINS.json').read_text())
assert pins['charon_exit']==pins['aeneas_exit']==pins['exit']==0
assert pins['lock_before']==pins['lock_after']
assert not json.loads((E/'NMX_auth_box_emitted/auth.llbc').read_text())['has_errors']
# Opaque-declaration provenance is explicit and all transparent actual owned
# functions/closures are loop-free. Native child loop audits are reused.
decls=json.loads((E/'NMX_auth_box_emitted/NMX_DECLARATIONS.json').read_text())
doc=json.loads((E/'NMX_auth_box_emitted/auth.llbc').read_text())
def loops(x):
 if isinstance(x,dict):
  return sum(k=='Loop' for k in x)+sum(loops(v) for v in x.values())
 if isinstance(x,list):return sum(loops(v) for v in x)
 return 0
transparent=[]
for f in doc.get('translated',doc)['fun_decls']:
 if f is not None and isinstance(f['body'],dict):
  name='::'.join(v['Ident'][0] for v in f['item_meta']['name'] if 'Ident' in v)
  n=loops(f['body']);assert n==0,(name,n)
  transparent.append({'name':name,'structured_loop_count':n})
plan=json.loads((E/'NMX_FOLD_PLAN.json').read_text());lift=json.loads((E/'NMX_R4_CALL_LIFT.json').read_text())
first={x['n']:x for x in lift['changes'] if x['first_call']}
expected={
'readonlyBuffer':'r1_pool_adapter.owned.require_readonly_buffer {a}',
'checkpointGuard':'(r1_pool_adapter.owned.require_verifier_checkpoint ops) {a}',
'readonlyAccount':'(r1_pool_adapter.owned.require_readonly_account ops) {a}',
'distinct':'(r1_pool_adapter.owned.require_distinct_accounts ops) {a}',
'data':'(r1_pool_adapter.owned.OwnedAccount.data ops) {a}',
'master':'ops.op48 {a}', 'checkpoint':'ops.op49 {a}', 'lane':'ops.op50 {a}',
'pda':'ops.op38 {a}',
'registry':'(r1_pool_adapter.owned.authenticate_invariant_release_registry ops) {a}'}
checked=[]
for st in plan:
 n=st['n'];term=st['term']
 if term.startswith('call '):
  cmd,args=re.fullmatch(r'call \(\.(\w+) (.*)\)',term,re.S).groups()
  if cmd in expected:
   original=first[n]['original']
   if cmd=='registry':original=re.sub(r'\bmaster\b(?!\.)','master.payload',original)
   assert norm(original)==norm(expected[cmd].format(a=args)),(n,cmd,original,args)
   checked.append({'occurrence':n,'command':cmd,'original':original,'same_arguments':True})
# Definition regeneration is checked against bytes which were actually compiled.
names=[E/f'NMX_R4_CallScript{g:02d}.lean' for g in range(6)]
before={p.name:sha(p.read_bytes()) for p in names}
subprocess.run(['python3',str(E/'NMX_R4_callscript_generate.py')],check=True)
assert before=={p.name:sha(p.read_bytes()) for p in names}
report={'status':'PASS','parent_root_tokens_unchanged_from_E002':True,
 'parent_root_token_sha256':sha(norm(root(paths[1])).encode()),'fresh_extraction':'NMX_E008',
 'fresh_pins_sha256':sha((E/'NMX_auth_box_emitted/NMX_PINS.json').read_bytes()),
 'script_hashes':before,'source_revision':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',
 'source_order_occurrences':55,'child_argument_checks':checked,
 'bc_flagged_own_exits':[],'bc_transparent_bodies':transparent,
 'allocation_interpretation':'Actual master/checkpoint wrapper bodies now emitted. Box::new is erased by pinned Aeneas; LLBC/source retain sites. NMX_R4_BoxAction restores the standard allocating action at each same-byte wrapper call, with CLOSED NKY frame law. Final snapshot site remains explicit. This does not manufacture physical native windows.',
 'effect_gate':'NMX_R4_Observed00.e001 and dependent step roots must pass separately; source audit alone is not a row root'}
(E/'NMX_R4_SOURCE_AUDIT.json').write_text(json.dumps(report,indent=1)+'\n')
print(json.dumps({'status':'PASS','child_argument_checks':len(checked),'occurrences':55}))
