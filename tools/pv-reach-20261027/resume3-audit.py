from pathlib import Path
import json,re,hashlib,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume3';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
rows=[json.loads(p.read_text()) for p in E.glob('receipt-[0-9]*.json')];names=[]
for r in rows:
 if r['accepted'] and 'NoCatchChunk' in r['target']:
  out=(E/f'out-{r["attempt"]}.log').read_text()
  names+=re.findall(r"'(R1Z\.PV_RE_NoCatchSource\.[^']+)' (?:depends|does not depend)",out)
names=sorted(set(names));suffixes=json.loads((E/'no-catch-suffix-manifest.json').read_text());support=json.loads((E/'whole-client-supports.json').read_text());a=[]
a.append(('PV_RE_FinalAudit3A','\n'.join(f'import R1Z.PV_RE_NoCatchChunk{i:03}' for i in range(50))+'\n'+'\n'.join('#print axioms '+n for n in names)+'\n'))
helpers=['R1Z.PV_RE_SourceSupport.'+x['function'] for x in support]
a.append(('PV_RE_FinalAudit3B','import R1Z.PV_RE_ClientSupport\n'+'\n'.join('#print axioms '+n for n in helpers)+'\n'))
mods=['PV_RE_FinalAudit3A','PV_RE_FinalAudit3B','PV_RE_ExcludedPoison','PV_RE_ShapeExclusions','PV_RE_PoisonOutcomes','PV_RE_ShapeRejection','PV_RE_NoCatchBoundary']
tops=['PV_RE_NoCatchCore.bind_noCatch','PV_RE_NoCatchCore.compose','PV_RE_NoCatchCore.exclusion_by_poisoning','PV_RE_ShapePoison.entry','PV_RE_ShapePoison.poisoned_entry','PV_RE_ShapePoison.success_distinguishes','PV_RE_ExcludedPoison.unchanged','PV_RE_ShapeExclusions.transfer','PV_RE_ShapeExclusions.withdrawal','PV_RE_PoisonOutcomes.exclusion','PV_RE_PoisonOutcomes.outer_ok_not_poison','PV_RE_PoisonOutcomes.different_error','PV_RE_ShapeRejection.equality_rejected','PV_RE_ShapeRejection.entry_diverges','PV_RE_NoCatchBoundary.local_certificates_insufficient']
a.append(('PV_RE_FinalAudit3C','\n'.join('import R1Z.'+m for m in mods)+'\n'+'\n'.join('#print R1Z.'+t+'\n#print axioms R1Z.'+t for t in tops)+'\n'))
for n,s in a:
 p=L/(n+'.lean')
 if '--check' in sys.argv:assert p.read_text()==s
 else:p.write_text(s)
manifest=dict(bind_certificate_count=len(names),support_helper_count=len(helpers),bind_certificates=names,support_helpers=helpers,targets=[dict(module='R1Z/'+n,sha256=hashlib.sha256(s.encode()).hexdigest()) for n,s in a],frozen_new_proof_modules=sorted({r['target'] for r in rows if r['accepted'] and 'FinalAudit3' not in r['target']}),prior_33_checks_reused_not_recompiled=True,release_closure_replay=False)
p=E/'audit-manifest.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==manifest
else:p.write_text(json.dumps(manifest,indent=2)+'\n')
print(len(names),'bind certificates;',len(helpers),'source support helpers')
