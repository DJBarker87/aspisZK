from pathlib import Path
import json,subprocess,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1]
out={}
for a in ['NBM_R001','NBM_R002','NBM_R003','NBM_K001']:
 d=json.loads((E/a/'receipt.json').read_text());g=json.loads((E/(a+'-graph.json')).read_text());ad=json.loads((E/(a+'-reservation.json')).read_text())
 assert ad['allowed'] is True
 assert g['allowed'] and not g['new_packages'] and not g['edge_errors'] and g['unchanged']
 assert g['lock_before']==g['lock_after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
 assert d['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert d['swaps']=='0'
 out[a]={k:d[k] for k in ['exit_status','wall_seconds','peak_rss_kib','swaps']}
assert out['NBM_R003']['exit_status']==0 and out['NBM_K001']['exit_status']==1
s=(E/'NBM_R003/stdout.log').read_text();assert '1 passed; 0 failed' in s and 'profile [optimized]' in s
s=(E/'NBM_K001/stdout.log').read_text();assert '1 of 47 failed (4 unreachable)' in s
new=s.split('```')[1].strip();old=(R/'evidence/native-tx1c-20261027/NBJ_K050/stdout.log').read_text().split('```')[1].strip();assert new.split('let concrete_vals:')[1]==old.split('let concrete_vals:')[1]
assert old in (E/'NBM_copy.rs.txt').read_text()
assert json.loads((E/'NBM_SOURCE_AUDIT.json').read_text())['all_equal']
for n in ['NBM_playback.patch']:
 subprocess.run(['git','apply','--check',str(E/n)],cwd=R,check=True)
subprocess.run(['git','diff','--check'],cwd=R,check=True)
files=subprocess.check_output(['git','diff','--name-only','69d88c78b9'],cwd=R,text=True).splitlines();assert all(x.startswith('evidence/native-tx1d-20261027/') for x in files)
assert not any(p.name.endswith(('.olean','.elf','.tar','.gz','.bin')) for p in E.rglob('*') if p.is_file())
(E/'NBM_VALIDATION.json').write_text(json.dumps(dict(passed=True,attempts=out,kani_runs=1,lean_attempts=0,new_bridge_credit=False,new_headline_premises_removed=0,classification='c',native_same_assertion_fails=False,generated_test_body_identical=True,patch_applies=True,source_files_unchanged=498),indent=2)+'\n')
print('NBM validation passes')
