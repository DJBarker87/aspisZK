from pathlib import Path
import json,hashlib,subprocess,difflib,re
E=Path(__file__).resolve().parent;REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
ks=[json.loads(p.read_text()) for p in sorted(E.glob('NBU_K*/receipt.json'))]
assert len(ks)==50,len(ks)
byname={x['module'].split('::')[-1]:x for x in ks}
positive=[];controls=[];timeouts=[];other=[]
for x in ks:
 log=(E/x['attempt']/'stdout.log').read_text();name=x['module'].split('::')[-1]
 graph=json.loads((E/(x['attempt']+'-graph.json')).read_text());assert graph['graph_matches_frozen'] and graph['lock_unchanged'] and graph['lock_before_sha256']==graph['frozen_lock_sha256']==graph['lock_after_sha256']
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 if 'timed out' in log or x['exit_status'] in [124,137]:timeouts.append(x['attempt']);continue
 if name.endswith('_negative'):
  assert x['exit_status']!=0 and 'VERIFICATION:- FAILED' in log
  assert 'unwinding assertion' not in log.lower() and 'could not compile' not in log
  controls.append(x['attempt'])
 elif x['exit_status']==0:
  if name!='NBU_result_control':
   neg=byname.get(name+'_negative');assert neg and neg['exit_status']!=0 and 'timed out' not in (E/neg['attempt']/'stdout.log').read_text(),name
  positive.append(x['attempt'])
 else:other.append(x['attempt'])
assert not other,other
lean=[json.loads(p.read_text()) for p in sorted(E.glob('NBU_L*/receipt.json'))]
for module in ['NBU_CopyWindows','NBU_SourceWindows','NBU_AnyWindow','NBU_Audit']:
 h=hashlib.sha256(Path('lean',module+'.lean').read_bytes()).hexdigest()
 matches=[x for x in lean if x['exit_status']==0 and x['source_hashes'].get('NBU_generated/'+module+'.lean')==h];assert matches,module
 for line in matches[-1]['print_axioms']:
  assert not any(k in line for k in ['sorryAx','native_decide','axiomAx']),line
  if 'depends on axioms:' in line:
   names=re.search(r'\[(.*?)\]',line).group(1).split(', ');assert set(names)<={'propext','Classical.choice','Quot.sound'}
subprocess.run(['git','diff','--exit-code',REV,'--','crates','programs'],check=True,capture_output=True)
a=[json.loads(p.read_text()) for p in sorted(E.glob('NBU_[GKL]*/receipt.json'))]
a.append(dict(attempt='NBU_L001',kind='lean-preflight',charged_slot=True,launched_lean=False,exit_status=1,module='NBU_CopyWindows',error='Own missing unchanged KMX_CopyMeaning dependency; privately built L002',evidence='NBU_L001-launcher.log',wall_seconds=None,peak_rss_kib=None,swaps=None,print_axioms='N/A: Lean not launched'))
(E/'NBU_ATTEMPTS.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in a))
summary=dict(kani_actual=len(ks),kani_positive=positive,kani_unpaired_no_credit=['NBU_K050'],kani_negative_controls=controls,kani_timeouts_excluded=timeouts,kani_other_failures=other,lean_actual=len(lean),lean_charged=len(lean)+1,lean_success=[x['attempt'] for x in lean if x['exit_status']==0],lean_rejected=[x['attempt'] for x in lean if x['exit_status']!=0],frozen_source=REV,repository_crates_programs_unchanged=True,kani_all_graphs_and_locks_match=True,KMX_patch_sha256=hashlib.sha256(Path('evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes()).hexdigest(),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),research_inspected_revision=subprocess.check_output(['git','rev-parse','research'],text=True).strip(),audit=next(x for x in lean if x['module']=='NBU_Audit'))
(E/'NBU_VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n')
# Complete scratch overlay; mandated KMX patch is separate and unchanged.
files={}
for parent,mod in [('pair_terminal','codecs'),('pair_forest_terminal','more')]:
 p=f'crates/aspis-statement/src/pool_v1/{parent}.rs';base=subprocess.check_output(['git','show',REV+':'+p],text=True);files[p]=base+f'\n#[cfg(kani)]\n#[path="NBU_{mod}.rs"]\nmod NBU_{mod};\n'
 if parent=='pair_terminal':files[p]+='\n#[cfg(kani)]\n#[path="NBU_decode.rs"]\nmod NBU_decode;\n'
p='crates/aspis-statement/src/lib.rs';base=subprocess.check_output(['git','show',REV+':'+p],text=True);files[p]='#![cfg_attr(kani, feature(allocator_api, next_index))]\n'+base+'\n#[cfg(kani)]\npub mod KMX_stubs;\n'
for mod in ['codecs','more','decode']:files[f'crates/aspis-statement/src/pool_v1/NBU_{mod}.rs']=(E/f'NBU_{mod}.rs.txt').read_text()
patch=''
for p,txt in files.items():
 base=subprocess.check_output(['git','show',REV+':'+p],text=True,stderr=subprocess.DEVNULL) if Path(p).exists() else ''
 patch+=''.join(difflib.unified_diff(base.splitlines(True),txt.splitlines(True),fromfile='a/'+p if base else '/dev/null',tofile='b/'+p))
(E/'NBU_harness.patch').write_text(patch)
print(json.dumps({k:summary[k] for k in ['kani_actual','lean_actual','lean_charged','kani_timeouts_excluded']}))
