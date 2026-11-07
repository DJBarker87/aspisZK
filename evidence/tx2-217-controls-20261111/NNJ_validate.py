"""Independent local receipt validation; no prover rerun or host infrastructure change."""
from pathlib import Path
import hashlib,json,lzma,re,subprocess
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
expected={
 'decoder_unimplied_stub':'NMX uninferred caller assertion',
 'decoder_modifies':'is assignable',
 'decoder_inverted_ensures':'Result<Box<PoolV1PairForestLaneStateV1>,ProgramError>',
 'assignment_inverted_ensures':'NMX_assign_post',
 'assignment_unimplied_stub':'NNJ unimplied other digest cell',
 'assignment_modifies':'is assignable',
 'KMX_slice_negative':'assertion failed',
 'KMX_ptr_negative':'assertion failed',
}
results=[]
for control in json.loads((E/'NNJ_CONTROLS.json').read_text()):
 a=control['attempt'];r=json.loads((E/a/'receipt.json').read_text());g=json.loads((E/(a+'-graph.json')).read_text());log=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 assert g['graph_matches_frozen'] and g['lock_unchanged'],a
 assert g['lock_before_sha256']==g['lock_after_sha256']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef',a
 assert g['KMX_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',a
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
 adm=json.loads((E/(a+'-admission.json')).read_text());assert adm['exit']==0 and adm['reservation']['allowed'] is True,a
 for n,h in r['source_hashes'].items():assert sha((E/a/'sources'/n).read_bytes())==h,(a,n)
 for p in (E/a).glob('*.xz'):
  q=p.with_suffix('.sha256');assert q.is_file() and sha(lzma.decompress(p.read_bytes()))==q.read_text().strip(),p
 features={g['packages'][i]['name']:f for i,f in g['features'].items()}
 assert {'pool-adapter','private-leaf-salts'}<=set(features['aspis-r1-cost-probe-program']),a
 assert {'default','private-leaf-salts','optimized-terminal','program-build'}<=set(features['aspis-r1-cost-probe']),a
 assert {'r0','pool-v1-kernel'}<=set(features['aspis-statement']),a
 m=re.search(r'\*\* (\d+) of (\d+) failed',log)
 if control['actual_verdict']=='PASS':assert r['exit_status']==0 and m and m[1]=='0' and 'VERIFICATION:- SUCCESSFUL' in log,a
 elif control['actual_verdict']=='FAIL':
  assert r['exit_status']==1 and m and int(m[1])>0 and 'VERIFICATION:- FAILED' in log,a
  assert expected[control['control']] in log,(a,control['control'])
 else:
  results.append(dict(attempt=a,status='no credit: nonsemantic failure',exit=r['exit_status']));continue
 results.append(dict(attempt=a,status='validated',expected=control['expected_verdict'],actual=control['actual_verdict'],failed_checks=int(m[1]),total_checks=int(m[2]),wall_seconds=r['wall_seconds'],peak_rss_kib=int(r['peak_rss_kib']),swaps=int(r['swaps'])))
# Verify source cut remains the exact frozen assignment after named argument substitution.
payload=json.loads(lzma.decompress((E.parent/'tx2-auth-20261111/NMX_FROZEN_PAYLOAD.json.xz').read_bytes()))
import base64
frozen=base64.b64decode(payload['programs/r1-cost-probe/src/r1_pool_adapter.rs']).decode();norm=lambda s:re.sub(r'\s+','',s)
s=frozen[frozen.index('        *node = decode_digest_canonical('):];s=s[:s.index('        if (next_leaf_index')]
expected_assignment=norm(s).replace('tree[start..start+32].try_into().map_err(|_|ProgramError::InvalidAccountData)?','window')
s=(E/'NNJ_assignment.rs').read_text();s=s[s.index('    *node = decode_digest_canonical('):];s=s[:s.index('    Ok(())')]
assert norm(s)==expected_assignment,'assignment source drift'
assert not subprocess.check_output(['git','diff','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','HEAD','--','crates','programs/r1-cost-probe','Cargo.lock'])
assert not subprocess.check_output(['git','diff','b936275465600469312d1f058cdc91ea2a11f3dc','HEAD','--','programs/aspis-pool'])
assert not subprocess.check_output(['git','diff','--','crates','programs','Cargo.lock'])
assert all(p.stat().st_size<=20_000_000 for p in E.rglob('*') if p.is_file())
output=dict(results=results,source_assignment_exact=True,shipped_frozen=True,new_Lean_roots=[],print_axioms='N/A: no new Lean declarations; no Lean scopes authorized beyond recording',rows_credited=[],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
(E/'NNJ_VALIDATION.json').write_text(json.dumps(output,indent=1)+'\n')
print(json.dumps(dict(validated=sum(x['status']=='validated' for x in results),uncredited=sum(x['status']!='validated' for x in results))))
