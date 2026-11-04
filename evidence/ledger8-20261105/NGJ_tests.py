"""Evidence admission mutation tests; never starts a prover."""
from pathlib import Path
import json,lzma,copy,collections,hashlib
E=Path(__file__).resolve().parent
J=lambda n:json.loads((E/n).read_text())
STD={'propext','Classical.choice','Quot.sound'}
def check(d,a,s):
 rows=d['rows'];assert len(rows)==len({r['row'] for r in rows})==599
 assert all(r['frozen_body_verified'] for r in rows)
 assert collections.Counter(r['composed_status'] for r in rows)=={'CLOSED':281,'OPEN':318}
 assert d['coverage']['all_rows']==d['NGJ_coverage']==dict(total=599,CLOSED=281,QUALIFIED=0,OPEN=318)
 assert d['NGJ_slices']['S']['CLOSED']==97 and d['NGJ_slices']['S']['roots_CLOSED']==7
 assert d['NGJ_slices']['Q']['roots_CLOSED']==2 and d['NGJ_slices']['D']['CLOSED']==43
 assert d['NGJ_security_target_established'] is False and d['NGJ_cold_release_replay'] is False
 manifest=J('NGJ_AUDIT_ROOTS.json');names=[r['root'] for r in a['results']]
 assert len(names)==len(set(names))==len(manifest['roots']) and set(names)==set(manifest['roots'])
 assert a['full_all_slices_status']=='FAILED_OWNER_CONFLICT' and a['verifier_status']=='PASS'
 assert all(set(r['walked_axioms'])<=STD and set(r['collect_axioms'])<=STD for r in a['results'])
 fixtures=a['fixtures'];assert len(fixtures)==8 and all(r['equal'] for r in fixtures)
 assert all(r['walked_axioms'] for r in fixtures[:4]) and all(not r['walked_axioms'] for r in fixtures[4:])
 assert a['same_proof_binary']['sha256'] and a['walker_conformance']['byte_identical']
 assert s['verifier']['dangling']==s['verifier']['incompatible_owners']==s['verifier']['import_mismatches']==0
 assert s['full_all_slices']['status']=='FAILED_IMPORT' and s['pool']['dangling']>0
 assert set(s['verifier']['required_roots_loaded'])=={'NGI_COMBINED_IMPORT','NFX_COMBINED_IMPORT','NFS_COMBINED_IMPORT','NFT_STAGE2_IMPORT','NFU_STAGE2_IMPORT','RPx_Deployed','NGJ_VERIFIER_IMPORT'}
 return True
if __name__=='__main__':
 d=json.loads(lzma.decompress((E/'NGJ_LEDGER.json.xz').read_bytes()));a=J('NGJ_AUDIT.json');s=J('NGJ_SCAN.json');assert check(d,a,s);tests=[]
 mutations=[('omit inventory row',lambda d,a,s:d['rows'].pop()),('duplicate row',lambda d,a,s:d['rows'].__setitem__(0,copy.deepcopy(d['rows'][1]))),('promote driver',lambda d,a,s:next(r for r in d['rows'] if r['row']=='TX1:330').update(composed_status='CLOSED')),('false target',lambda d,a,s:d.update(NGJ_security_target_established=True)),('false cold replay',lambda d,a,s:d.update(NGJ_cold_release_replay=True)),('omit audit root',lambda d,a,s:a['results'].pop()),('duplicate audit root',lambda d,a,s:a['results'].__setitem__(0,copy.deepcopy(a['results'][1]))),('nonstandard axiom',lambda d,a,s:a['results'][0]['walked_axioms'].append('untrusted')),('missing fixture',lambda d,a,s:a['fixtures'].pop()),('planted axiom missing',lambda d,a,s:a['fixtures'][0].update(walked_axioms=[])),('mutation axiom survives',lambda d,a,s:a['fixtures'][-1].update(walked_axioms=['propext'])),('dangling verifier',lambda d,a,s:s['verifier'].update(dangling=1)),('owner conflict waived',lambda d,a,s:a.update(full_all_slices_status='PASS')),('Pool inherited defect waived',lambda d,a,s:s['pool'].update(dangling=0)),('missing scanner root',lambda d,a,s:s['verifier']['required_roots_loaded'].pop()),('wrong D headline',lambda d,a,s:d['NGJ_slices']['D'].update(CLOSED=47))]
 for name,f in mutations:
  dd,aa,ss=copy.deepcopy(d),copy.deepcopy(a),copy.deepcopy(s);f(dd,aa,ss)
  try:check(dd,aa,ss)
  except AssertionError:tests.append(dict(name=name,result='REJECTED'))
  else:raise AssertionError('mutation accepted '+name)
 (E/'NGJ_TESTS.json').write_text(json.dumps(dict(valid=True,mutations=tests,proof_launches=0),indent=1)+'\n');print('All',len(tests),'mutations rejected')
