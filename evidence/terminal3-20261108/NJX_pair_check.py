from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent;P=E.parent/'terminal-20261107';L=E.parent/'terminal2-20261108'
pairs=[(P,f'NJB_K{k:03}',f'NJB_K{k+1:03}')for k in [98,102]+list(range(104,132,2))]+[(L,f'NJL_K{k:03}',f'NJL_K{k+1:03}')for k in [47,49,51,53,55,57,61]]
pairs += [(E,'NJX_K001','NJX_K002')]
if (E/'NJX_K004'/'receipt.json').exists():pairs += [(E,'NJX_K003','NJX_K004')]
rows=[]
for d,a,b in pairs:
 r=[json.loads((d/x/'receipt.json').read_text())for x in [a,b]]
 g=[json.loads((d/(x+'-graph-check.json')).read_text())for x in[a,b]]
 lock=[json.loads((d/(x+'-lock-check.json')).read_text())for x in[a,b]]
 out=[(d/x/'stdout.log').read_text()for x in[a,b]]
 assert r[0]['exit_status']==0 and r[1]['exit_status']!=0,(a,b)
 assert 'VERIFICATION:- SUCCESSFUL' in out[0] and 'VERIFICATION:- FAILED' in out[1],(a,b)
 assert all(x['graph_matches_frozen']for x in g)and all(x['unchanged']for x in lock),(a,b)
 h=[x['source_hashes']for x in r];diff=[n for n in set(h[0])|set(h[1])if h[0].get(n)!=h[1].get(n)]
 setup_delta=None
 if a=='NJB_K098':
  assert set(diff)=={'NJB_SOURCE_PINS.json','NJB_install_windowed_gate.py'}
  pins=[json.loads((d/z/'sources/NJB_SOURCE_PINS.json').read_text())for z in[a,b]]
  changed={n for n in set(pins[0])|set(pins[1])if pins[0].get(n)!=pins[1].get(n)}
  assert changed=={'crates/aspis-statement/src/pool_v1/NJB_windowed.rs','crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs'}
  assert h[0]['NJB_windowed.rs.txt']==h[1]['NJB_windowed.rs.txt']
  assert pins[1]['crates/aspis-statement/src/pool_v1/NJB_windowed.rs']==h[0]['NJB_windowed.rs.txt']
  installer=(d/a/'sources/NJB_install_windowed_gate.py').read_text()
  assert "assert hashlib.sha256(p.read_bytes()).hexdigest()==pins[q]" in installer
  assert "mod NJB_windowed_native;" in installer and "NJB_gate.py" in installer
  setup_delta=dict(reason='First immutable harness installation only; native payload, gate, KMX and all other source inputs identical. Positive installer asserts prior source pin, appends cfg(kani) module without changing its body, then calls SAME strict validator. Negative uses installed tree directly.',input_differences=diff,changed_pins=sorted(changed),installer_sha256=h[0]['NJB_install_windowed_gate.py'])
 else:assert not diff,(a,b,diff)
 rows.append(dict(positive=a,negative=b,evidence=str(d),both_reach_verification=True,positive_exit=r[0]['exit_status'],negative_exit=r[1]['exit_status'],frozen_graph=True,lock_unchanged=True,identical_source_hashes=not diff,reviewed_first_install=setup_delta,receipts=[str(d/a/'receipt.json'),str(d/b/'receipt.json')]))
patch=E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch';sha=hashlib.sha256(patch.read_bytes()).hexdigest();assert sha=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
(E/'NJX_NATIVE_PAIRS.json').write_text(json.dumps(dict(pairs=rows,kmx_patch_sha256=sha,all_pairs_checked=True),indent=2))
print('Native pair/frozen graph/unchanged lock/exact KMX validation passed: '+str(len(rows)))
