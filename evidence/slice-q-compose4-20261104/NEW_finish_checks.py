"""Final metadata-only evidence audit; no new formal scopes."""
from NEW_inverse_checks import *
import collections,copy
labels=[2,3,4,6,7,9,10,12,13,16,18,25,29,30,32,37,40,44,46,48,50,54,56,58,62,77,78,79]
generated=obj(E/'NEW_GENERATED.json');accepted=[]
for n in labels:
 a=f'NEW_L{n:03}';r=receipt(a,0);mod=r['module'];path=mod.replace('.','/')+'.lean';src=E/path
 if not src.exists():src=E/generated[mod]['path']
 assert sha(src)==r['source_hashes'][path],('accepted source drift',a,str(src))
 for line in r['print_axioms']:
  m=re.search(r'depends on axioms: \[([^\]]*)\]',line,re.S)
  if m:assert {x.strip()for x in m[1].split(',')if x.strip()}<={'propext','Classical.choice','Quot.sound'},(a,line)
  else:assert 'does not depend on any axioms'in line,(a,line)
 accepted.append(dict(attempt=a,module=mod,source=str(src.relative_to(E)),sha256=sha(src),print_axioms=r['print_axioms']))
(E/'NEW_PROOF_AUDIT.json').write_text(json.dumps(dict(accepted=accepted,excluded_final_module='NEW_L080: exit1; no zero_body/zero_loop/zero_loop_frame credit',standard_axioms_only=True,root_math=['NEW_L079'],security_target_established=False),indent=1)+'\n')
from NEW_geometry_checks import pair
pairs=[('NEW_K041','NEW_K042'),('NEW_K043','NEW_K044'),('NEW_K045','NEW_K046','NEW_K047'),('NEW_K048','NEW_K049','NEW_K050'),('NEW_K051','NEW_K052','NEW_K053'),('NEW_K054','NEW_K055','NEW_K056'),('NEW_K057','NEW_K058','NEW_K059'),('NEW_K060','NEW_K061'),('NEW_K062','NEW_K063'),('NEW_K064','NEW_K065'),('NEW_K066','NEW_K067'),('NEW_K068','NEW_K069','NEW_K070'),('NEW_K071','NEW_K072'),('NEW_K073','NEW_K074'),('NEW_K077','NEW_K078'),('NEW_K079','NEW_K080'),('NEW_K081','NEW_K082','NEW_K083'),('NEW_K084','NEW_K085','NEW_K086'),('NEW_K095','NEW_K096'),('NEW_K141','NEW_K142'),('NEW_K169','NEW_K170','NEW_K171','NEW_K172','NEW_K173','NEW_K174'),('NEW_K175','NEW_K176','NEW_K177','NEW_K178'),('NEW_K179','NEW_K180','NEW_K181'),('NEW_K182','NEW_K183','NEW_K184','NEW_K185'),('NEW_K186','NEW_K187','NEW_K188','NEW_K189'),('NEW_K190','NEW_K191'),('NEW_K192','NEW_K193')]
checks=[pair(*p)for p in pairs]
# Same baseline flags, source bytes and approved patch for copy fidelity groups.
def cfg(a):return obj(E/a/'receipt.json')
copy_groups=[('NEW_K077',['NEW_K041','NEW_K043']),('NEW_K079',['NEW_K071','NEW_K073']),('NEW_K064',['NEW_K045','NEW_K048','NEW_K051','NEW_K054','NEW_K057','NEW_K060','NEW_K062','NEW_K068']),('NEW_K095',['NEW_K081','NEW_K084']),('NEW_K192',['NEW_K169','NEW_K175','NEW_K182','NEW_K186','NEW_K190'])]
for c,used in copy_groups:
 for a in used:
  assert cfg(c)['source_hashes']==cfg(a)['source_hashes'],(c,a,'copy source configuration differs')
  assert cfg(c)['env']==cfg(a)['env'],(c,a,'copy environment differs')
(E/'NEW_NATIVE_PARTIAL_AUDIT.json').write_text(json.dumps(dict(pairs=checks,copy_groups=copy_groups,root_status='OPEN',composed_credit=False,exclusions=['All Kani receipts through K039 lack required offline environment','K040 compiler ICE','K075 absent control mutation','K087/K097/K117/K143 timeouts','K141/K142 has no matching source-configuration copy control: no full native/copy/root credit'],function_pointer_dependent_passes_credited=[],writable_static_passes_credited=[]),indent=1)+'\n')
rows=[obj(p)for p in sorted(E.glob('NEW_*/receipt.json'))];counts=collections.Counter(r['kind']for r in rows)
assert counts['kani']==110 and counts['lean']==80 and counts['extract']==4 and counts['native']==4,counts
for r in rows:assert int(r['swaps'])==0 and r['limits']==LIMITS
metrics=[]
for r in rows:
 v={k:r.get(k)for k in ['attempt','kind','target','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','print_axioms','limits']};v['receipt']=r['attempt']+'/receipt.json';metrics.append(v)
(E/'NEW_METRICS.json').write_text(json.dumps(metrics,indent=1)+'\n')
(E/'NEW_BUDGET.json').write_text(json.dumps(dict(limits=dict(kani=110,lean=80,extract=10),executed=dict(counts),unused_extraction=6,why_no_more_extraction='Remaining rows need native caller/callee/frame association and/or a checked Lean join. Actual geometry and inverse are already extracted; another reference/emission cannot close these obligations with both primary budgets exhausted.',excluded_pre_scope='NEW_K001 cancelled before any scope; not counted',scope_labels_are_not_execution_counts=True,swaps=0,os_memory_kills=0,internal_lean_memory_failures=['NEW_L063','NEW_L068'],timeouts=['NEW_K087','NEW_K097','NEW_K117','NEW_K143'],caps=LIMITS,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()),indent=1)+'\n')
print(json.dumps(dict(counts=counts,proof_modules=len(accepted),native_partial_pairs=len(checks),swaps=0)))
