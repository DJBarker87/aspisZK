from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
paths=['crates/aspis-r1-cost-probe/src/'+x for x in ['verifier.rs','candidate.rs','eight_way.rs','lib.rs']]
sources={p:subprocess.check_output(['git','show',rev+':'+p]).decode() for p in paths}
result={'revision':rev,'source_hashes':{p:hashlib.sha256(s.encode()).hexdigest() for p,s in sources.items()},'sites':[],'scope':'default frozen release; audit-eight-way is cfg-excluded and forbidden for SBF/program builds'}
for p,s in sources.items():
 for i,line in enumerate(s.splitlines(),1):
  if re.search(r'\bcheckpoint\s*\(',line):
   result['sites'].append({'path':p,'line':i,'source':line,'default_release':p.endswith('/candidate.rs'),'status':'OPEN: full S1S7S8StateProvenance not established' if p.endswith('/candidate.rs') else 'EXCLUDED: audit-eight-way cfg; arbitrary k/variant domain differs from checkpoint leaf'})
result['guards']={p:[{'line':i,'source':line} for i,line in enumerate(s.splitlines(),1) if 'audit-eight-way' in line or 'pub use candidate::' in line] for p,s in sources.items() if p.endswith(('verifier.rs','lib.rs'))}
(E/'XSg_CHECKPOINT_SITES.json').write_text(json.dumps(result,indent=2)+'\n')
