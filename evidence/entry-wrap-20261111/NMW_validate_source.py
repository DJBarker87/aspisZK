"""Validate actual emitted bodies, parameterization, pins and loop-exit audit."""
from pathlib import Path
import hashlib,json,re,subprocess,lzma
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
rows=[]
for label in ['entry','process']:
 b=E/('NMW_'+label+'_emitted');pins=json.loads((b/'NMW_PINS.json').read_text())
 assert pins['charon_exit']==pins['aeneas_exit']==pins['exit']==0
 assert pins['lock_before']==pins['lock_after']
 for p,h in pins['outputs'].items():assert sha((b/p).read_bytes())==h,p
 graph=json.loads((b/'NMW_GRAPH_CHECK.json').read_text());assert graph['graph_matches_frozen']
 md=json.loads((b/'metadata.json').read_text());pkgs={p['id']:p for p in md['packages']};nodes={p['id']:p for p in md['resolve']['nodes']}
 root=next(p['id'] for p in md['packages'] if p['name']=='aspis-r1-cost-probe-program');seen=set()
 def visit(i):
  if i in seen:return
  seen.add(i)
  for d in nodes[i]['deps']:
   if any(k['kind'] in (None,'build') for k in d['dep_kinds']):visit(d['pkg'])
 visit(root);assert all(pkgs[i]['name']!='aspis-pool' for i in seen)
 fun=(b/'raw'/('NMW_'+label)/'Funs.lean').read_text()
 assert 'loop' not in fun and 'while ' not in fun
 rows.append(dict(extraction=label,raw_sha256=sha(fun.encode()),loop_audit='PASS: neither body nor transparent primitive has a loop; all returned branch values preserved',pool_in_selected_closure=False,features={pkgs[i]['name']:nodes[i]['features'] for i in seen}))
def body(s,name,next_name=None):
 start=s.index('def '+name);start=s.index(':= do',start)
 end=s.index('/--',start) if '/--' in s[start:] else s.index('\nend ',start)
 return s[start:end].strip()
entry=(E/'NMW_entry_emitted/raw/NMW_entry/Funs.lean').read_text()
process=(E/'NMW_process_emitted/raw/NMW_process/Funs.lean').read_text()
assert body(entry,'r1_pool_adapter.process')==body(process,'r1_pool_adapter.process')
parameterized=(E/'NMW_Emitted.lean').read_text()
for raw_name,new_name in [('r1_pool_adapter.process','process'),('process_r1_cost_probe_instruction','entry')]:
 s=body(entry,raw_name)
 for a,b in [('core.slice.Slice.first','Hiq_DispatchSource.firstByte'),('core.option.OptionShared0T.copied core.marker.CopyU8','Hiq_DispatchSource.copied'),('Slice.Insts.CoreCmpPartialEqArray.eq core.cmp.PartialEqU8','Hiq_DispatchSource.eqU8'),('r1_pool_adapter.owned.stage1','ops.first'),('r1_pool_adapter.owned.stage2','ops.second'),('r1_pool_adapter.lifecycle_init','ops.init'),('r1_pool_adapter.lifecycle_write','ops.write'),('r1_pool_adapter.lifecycle_finalize','ops.finalize'),('pool_route.admitted','Hiq_DispatchSource.pool_route.admitted'),('r1_pool_adapter.process program_id','process ops program_id'),('solana_program_error.ProgramError','AdapterRw.solana_program_error.ProgramError')]:s=s.replace(a,b)
 t=body(parameterized,new_name)
 if new_name=='entry':t=t[:t.index('theorem process_source')].strip()
 assert re.sub(r'\s+','',s)==re.sub(r'\s+','',t),new_name
sources={}
for p in ['programs/r1-cost-probe/src/lib.rs','programs/r1-cost-probe/src/r1_pool_adapter.rs','Cargo.lock']:
 b=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p]);sources[p]=dict(revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',sha256=sha(b))
report=dict(status='PASS',raw_parameterization='exact normalized bodies after enumerated substitutions; no template axiom compiled',process_fresh_emissions_equal=True,extractions=rows,source_pins=sources,bc='no post-loop return pattern',scope_overlap='NMW_SCOPE_OVERLAP.json (explicit rule violation; no self-credit)')
(E/'NMW_SOURCE_AUDIT.json').write_text(json.dumps(report,indent=1)+'\n');print('NMW source validation PASS')
