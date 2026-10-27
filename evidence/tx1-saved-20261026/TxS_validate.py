from pathlib import Path
import hashlib,json,re,subprocess
OUT=Path(__file__).resolve().parent;ROOT=OUT.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts={int(p.parent.name.split('_')[1]):json.loads(p.read_text()) for p in OUT.glob('TxS_[0-9][0-9][0-9]/receipt.json')}
preflight={38,43}
assert set(receipts)==set(range(1,101))-preflight
passes={n:r for n,r in receipts.items() if r['exit_status']==0}
failures={n:r for n,r in receipts.items() if r['exit_status']!=0}
assert len(receipts)==98
for n,r in receipts.items():
 assert r['swaps']=='0'
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert '-M7000' in r['command'] and '-j1' in r['command']
 assert r['source_revision'] and r['source_hashes']
 for file,h in r['source_hashes'].items():assert sha(OUT/f'TxS_{n:03}'/'sources'/file)==h
# Exact final declaration audits (theorem statements and accepted-axiom inventory).
index=json.loads((OUT/'TxS_audit-index.json').read_text());assert len(index)==34
axioms=[]
for row in index:
 n=int(row['attempt'].split('_')[1]);assert n in passes
 log=(OUT/row['attempt']/'stdout.log').read_text()
 blocks=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log,re.S)
 assert len(blocks)==1 and blocks[0][0]==row['declaration'],(n,blocks)
 names={s.strip() for s in blocks[0][1].split(',')}
 assert names<={'propext','Classical.choice','Quot.sound'},(n,names)
 assert 'sorryAx' not in log and 'error:' not in log
 axioms.append({**row,'axioms':sorted(names),'evidence':row['attempt']+'/stdout.log'})
# Each final source matches a successful receipt EXACTLY, including its audit inputs.
sources=[]
for file in sorted((ROOT/'lean').glob('TxS_*.lean')):
 h=sha(file);matches=[n for n,r in passes.items() if r['source_hashes'].get(file.name)==h]
 assert matches,file
 n=max(matches);s=file.read_text()
 assert not re.search(r'(^|\s)(sorry|admit|native_decide)(\s|$)|^axiom\s|set_option\s+(maxHeartbeats|maxRecDepth)',s,re.M),file
 sources.append({'path':str(file.relative_to(ROOT)),'sha256':h,'passing_attempt':f'TxS_{n:03}','selected_direct_objects':passes[n]['deps_fingerprint']['selected_objects']})
# The unused unprefixed dependency alternatives must not enter the final audit graph.
for n in range(67,101):
 selected=passes[n]['deps_fingerprint']['selected_objects']
 assert 'LiteralMatchingFacts.olean' not in selected and 'LiteralOpeningFunctionalFacts.olean' not in selected
changed=subprocess.check_output(['git','diff','--name-only','a0c5e1f66a9d16f76a22bd77fb0bc499a64a9978','HEAD'],cwd=ROOT,text=True).splitlines()
assert all(p.startswith('lean/TxS_') or p.startswith('evidence/tx1-saved-20261026/') for p in changed)
summary={'budget':{'conservatively_charged_submissions':100,'actual_lean_invocations':98,'preflight_exclusions':sorted(preflight),'passing_invocations':len(passes),'excluded_diagnostic_invocations':sorted(failures),'unchanged_dependency_builds':[44,45],'kani_runs':0},'final_theorems':axioms,'sources':sources,'peak_rss_kib':max(int(r['peak_rss_kib']) for r in receipts.values()),'all_swaps_zero':True,'all_caps_verified':True,'source_revision_anchor':'6f36ea5f84','final_audit_revision':passes[100]['source_revision'],'final_top':{k:passes[98][k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']},'scope':'Focused coherent cache/declaration audit, not a fresh release closure or package replay','no_shipped_changes':True,'inherited_elf_pins_not_rebuilt':{'default':'f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','devnet':'63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','Pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'}}
(OUT/'TxS_validation.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:summary[k] for k in ['budget','peak_rss_kib','all_swaps_zero','final_top']},indent=2))
