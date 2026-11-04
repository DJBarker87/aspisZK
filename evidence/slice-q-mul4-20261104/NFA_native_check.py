from pathlib import Path
import json,hashlib,copy,re
E=Path(__file__).resolve().parent
obj=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def check(a,expected,harness):
 p=E/a;r=obj(p/'receipt.json');ad=obj(E/(a+'-admission.json'));log=(p/'stdout.log').read_text()
 assert ad['exit']==0 and ad['reservation']['allowed'] is True
 assert r['exit_status']==expected and r['env']['CARGO_NET_OFFLINE']=='true'
 assert r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert 'CBMC timed out' not in log and 'excessive memory consumption' not in log
 assert ('VERIFICATION:- FAILED' if expected else 'VERIFICATION:- SUCCESSFUL') in log
 cmd=r['native_command'];assert cmd[cmd.index('--harness')+1]==harness
 assert '--locked' not in cmd
 graph=obj(E/(a+'-graph-check.json'));assert graph['exact_frozen_selected_graph'] and graph['graph_matches_frozen']
 assert graph['resolved_features_all_crates']
 assert obj(E/(a+'-lock-check.json'))['unchanged'] is True
 assert obj(E/(a+'-rule16-check.json'))['static_declarations']==[]
 assert obj(E/(a+'-frozen-source-check.json'))['passed']
 for name,h in r['source_hashes'].items():assert sha(p/'sources'/name)==h
 return r
def envbase(r):
 env=copy.deepcopy(r['env']);env['RUSTFLAGS']=re.sub(r' --cfg NFA_wrong_\w+$','',env['RUSTFLAGS']);return env
base=check('NFA_K010',0,'NFA_copy::KMX_checks::KMX_ptr_correct');wrong=check('NFA_K011',1,'NFA_copy::KMX_checks::KMX_ptr_wrong')
assert base['source_hashes']==wrong['source_hashes'] and base['env']==wrong['env']
pairs=[]
for pos,neg,name,cfg in [('NFA_K001','NFA_K002','dots_outer_cursor','NFA_wrong_dots_cursor'),('NFA_K003','NFA_K004','dots_cursor_remaining','NFA_wrong_cursor_remaining'),('NFA_K005','NFA_K006','dots_selected_g_frame','NFA_wrong_selected_g'),('NFA_K007','NFA_K008','dots_wrapper_window','NFA_wrong_wrapper_window')]:
 h='fast_pairing::canonical::NFA_dot_ctor::'+name;p=check(pos,0,h);n=check(neg,1,h)
 assert p['source_hashes']==n['source_hashes'] and p['source_hashes']==base['source_hashes']
 assert envbase(p)==envbase(n)==base['env']
 assert n['env']['RUSTFLAGS']==p['env']['RUSTFLAGS']+' --cfg '+cfg
 for suffix in ['-graph-check.json','-tool-check.json']:
  assert obj(E/(pos+suffix))==obj(E/(neg+suffix))==obj(E/('NFA_K010'+suffix))==obj(E/('NFA_K011'+suffix))
 pairs.append(dict(positive=pos,negative=neg,harness=h,status='LOCAL_NATIVE_PAIR_PASS',copy_controls=['NFA_K010','NFA_K011']))
patch=E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch';assert sha(patch)=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
out=dict(status='LOCAL_NATIVE_CUTS_ONLY',copy_patch_sha256=sha(patch),pairs=pairs,excluded=[dict(attempt='NFA_K009',reason='own incorrect harness selector; no proof launched; corrected K010/K011')],multiplication_proved_in_kani=False,function_pointer_credits=[],writable_static_credits=[],composed_rows_closed=[],remaining=['specialized native StepBy full prestate/model association','arbitrary parser/term/caller domain assembly','full outer loop and tail composition','incoming slice-Q edge certificates'])
(E/'NFA_NATIVE_CHECK.json').write_text(json.dumps(out,indent=2)+'\n');print(out['status'])
