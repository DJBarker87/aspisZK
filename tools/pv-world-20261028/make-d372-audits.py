from pathlib import Path
import subprocess,re,json,hashlib
R=Path(__file__).resolve().parents[2];D=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-world-20261028'
changed=subprocess.check_output(['git','diff','--name-only','95740e6864','--','docs/research/v8-r0-zk-20261009/lean/R1Z'],cwd=R,text=True).splitlines()
modules=[];queries=[]
for p in sorted(changed):
 q=R/p
 if not q.exists() or not q.stem.startswith('PV_W_') or q.stem=='PV_W_LoopInspect':continue
 if q.stem in ['PV_W_D372Audit','PV_W_D372Replay']:continue
 s=q.read_text();ns=re.search(r'^namespace (\S+)',s,re.M)
 assert ns,p
 modules.append('R1Z.'+q.stem)
 queries += [ns[1]+'.'+name for name in re.findall(r'^theorem\s+(\w+)',s,re.M)]
body='import R1Z.PV_FXM_AuditAxioms\n'+''.join('import '+m+'\n' for m in modules)
body+='\n'+''.join('#print axioms '+q+'\n' for q in queries)
body+='#print axioms R1Z.PV_W_Enriched.project_threaded\n'
(D/'PV_W_D372Audit.lean').write_text(body)
main=['R1Z.PV_W_ReachedThreading.entry_source','R1Z.PV_W_ReachedThreading.entry_threaded','R1Z.PV_W_ReachedThreading.project_run','R1Z.PV_W_PrivateSaltsLoop.world_threaded','R1Z.PV_W_MemoryCombined.current_selector','R1Z.PV_W_Ownership.drop_slot_once','R1Z.PV_W_ZeroizingBridge.wrapper_outcome']
(D/'PV_W_D372Replay.lean').write_text('import R1Z.PV_W_D372Audit\n'+''.join('#print axioms '+q+'\n' for q in main))
(E/'d372-audit-plan.json').write_text(json.dumps(dict(scope='focused current source and dependency replay; not a deployment/frozen-manifest release',imports=modules,queries=queries,fxmem_queries=79,final_ids=[50497,50498,50499],excluded_diagnostic='PV_W_LoopInspect',uncompiled_fold_draft_revision='d216687bb4',rows_closed=[],endpoint_premises_removed=0),indent=2)+'\n')
print(len(modules),'current source modules;',len(queries)+1,'world axiom queries')
