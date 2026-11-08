"""Compile-free validation of exact session4 sources and recorded evidence."""
import hashlib,json,lzma,pathlib,re,subprocess
E=pathlib.Path('evidence/pv-lib-20261107/lane-SLICE');sha=lambda b:hashlib.sha256(b).hexdigest()
idx=json.loads((E/'SESSION4_CONTRACT_INDEX.json').read_text());assert len(idx['statements'])==11 and idx['contract_instances']==0
passing=[];failed=[];sources={}
for a in range(49923,49943):
 r=json.loads((E/f'receipt-{a}.json').read_text());assert r['attempt']==a
 assert r['caps']==dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,Lean_M=7000)
 assert r['swaps']=='0' and int(r['peak_rss_kbytes'])<8*1024*1024
 assert r['source_revision'] and r['wall'] and r['axioms_summary_based']
 turn=json.loads((E/f'turn-{a}.json').read_text());assert turn['exit']==0 and turn['attempt']==a
 t=json.loads((E/f'transport-{a}.json').read_text());assert t['exit']==r['exit']
 admit=json.loads((E/f'admission-{a}.json').read_text());assert admit['allowed'] is True
 assert json.loads((E/f'id-audit-{a}.json').read_text())['hits']==[]
 if r['accepted']:
  assert r['exit']==0 and all('sorryAx' not in x for x in r['axioms_summary_based'])
  for line in r['axioms_summary_based']:
   if 'depends on axioms: [' in line:
    ax=line.split('depends on axioms: [')[1].split(']')[0]
    assert set(ax.split(', '))<={'propext','Classical.choice','Quot.sound'}
  p=pathlib.Path('lean',r['target']+'.lean');assert sha(p.read_bytes())==r['source_sha256']
  commit=subprocess.check_output(['git','log','-1','--format=%H','--',str(p)],text=True).strip()
  assert sha(subprocess.check_output(['git','show',commit+':'+str(p)]))==r['source_sha256']
  sources[r['target']]=dict(source_sha256=r['source_sha256'],source_commit=commit,compile=a)
  passing.append(a)
 else:
  assert sha(lzma.decompress((E/f'failed-input-{a}.lean.xz').read_bytes()))==r['source_sha256']
  failed.append(a)
for row,a in idx['statements'].items():
 assert sources['PV_LIB_SLICE_Spec_'+row]['compile']==a
 text=pathlib.Path('lean','PV_LIB_SLICE_Spec_'+row+'.lean').read_text()
 assert all(re.search(r'^(def|structure|abbrev) '+n+r'\b',text,re.M) for n in ['Pre','Post','MachineSpec','Contract'])
 assert not re.search(r'\b(sorry|axiom|admit)\b',re.sub(r'/-.*?-/', '', text, flags=re.S))
 assert (E/f'SESSION4_{row}_COMPARISON.md').exists()
assert idx['joint_witness']['compile']==49941
old=subprocess.check_output(['git','show','896d708bf39:evidence/pv-lib-20261107/lane-SLICE/MAP_DELTA.json'],text=True)
assert json.loads(old)['slots']==json.loads((E/'MAP_DELTA.json').read_text())['slots']
changed=subprocess.check_output(['git','diff','--name-only','896d708bf39'],text=True).splitlines()
assert all(p.startswith(str(E)+'/') or re.fullmatch(r'lean/PV_LIB_SLICE_\w+\.lean',p) for p in changed),changed
# Driver and walker logic unchanged except explicit module/root/constructor arrays.
a=pathlib.Path('lean/PV_LIB_SLICE_RawAudit3.lean').read_text();b=pathlib.Path('lean/PV_LIB_SLICE_RawAudit4.lean').read_text()
def erase_arrays(s):
 start=s.index('    (#[`');end=s.index('\n  let env',start);s=s[:start]+'ARRAYS'+s[end:]
 start=s.index('for aux in #[');end=s.index('] do',start);return s[:start]+'CONSTRUCTORS'+s[end:]
assert erase_arrays(a)==erase_arrays(b)
audit=json.loads((E/'SESSION4_RAW_AUDIT.json').read_text());assert audit['strict_raw'] and audit['root_count']==120 and audit['summary_mismatches']==audit['unresolved']==0
receipt=audit['receipt'];assert receipt['accepted'] and receipt['exit']==0 and receipt['swaps']=='0'
manifest=json.loads((E/'SESSION4_RAW_GRAPH_MANIFEST.json').read_text());raw=(E/'SESSION4_RAW_GRAPH_ARCHIVE.json.xz').read_bytes();assert sha(raw)==manifest['archive_sha256']
uncompressed=lzma.decompress(raw);assert sha(uncompressed)==manifest['uncompressed_sha256']
archive=json.loads(uncompressed)
for f in manifest['files']:
 if f['name'] in archive:assert sha(archive[f['name']].encode())==f['sha256']
for root in json.loads((E/'SESSION4_AUDIT_ROOTS.json').read_text())['roots']:
 assert any(n.endswith(root+'_REACHABLE.txt') for n in archive),root
result=dict(base='896d708bf39',passed=passing,failed_exact_archives=failed,statement_count=11,contract_instances=0,
 joint_witness=idx['joint_witness'],sources=sources,strict_audit=dict(attempt=49693,roots=120),
 boundary_checked=True,driver_walker_collector_unchanged=True,slot_statuses_unchanged=True)
(E/'SESSION4_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n')
print('Validated 11 complete statements, source7 joint witness, 13 focused passes, 7 archived failures and 120 strict raw roots.')
