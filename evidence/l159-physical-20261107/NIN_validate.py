"""Fail-closed validation of NIN source, receipts, raw roots, import scan and ledger."""
from pathlib import Path
import json,hashlib,lzma,re,sys,copy
E=Path(__file__).resolve().parent
STANDARD={'propext','Classical.choice','Quot.sound'}
def require(yes,message):
 if not yes:raise AssertionError(message)
def validate_roots(expected,results):
 by={r['root']:r for r in results}
 require(set(expected)<=set(by),'missing raw audit root')
 for n in expected:
  require(set(by[n]['walked_axioms'])<=STANDARD,'nonstandard raw axiom')
  require(not by[n].get('unresolved',[]),'unresolved raw reference')
 return [r for r in results if r.get('equal')is False]
def validate_scan(rows):
 require(bool(rows),'missing scan')
 for r in rows:
  require(not r['dangling'],'dangling reference')
  require(not r.get('duplicate_owners',[]),'incompatible declaration owners')
  require(r['imports_match']is True,'missing/source-inconsistent imports')
 modules={r['module']for r in rows}
 require('NGL_MapReference.Types'not in modules,'forbidden duplicate map owner')
 require('NIM_MapReference.Types'in modules,'missing canonical map owner')
 require('NIN_COMBINED_IMPORT'in modules and 'RPx_Deployed'in modules,'missing combined headline')
def validate_admission(a):
 require(a['exit']==0 and a['reservation'].get('allowed')is True,'unadmitted scope')
def validate_ledger(x):
 require(x['row_promotions']==[]and x['row_changes']==[]and x['trust_rows_added']==[]and x['game_changes']==[],'unauthorized promotion/amendment')
def main():
 manifest=json.loads((E/'NIN_AUDIT_ROOTS.json').read_text());results=[]
 for i,names in enumerate(manifest['groups']):
  r=json.loads((E/f'NIN_audit/batch{i}/proof{i}.json').read_text())
  results+=r['results']
  require({x['root']for x in r['results']}==set(names),'group selectors differ')
 disagreements=validate_roots(manifest['roots'],results)
 fixtures=json.loads((E/'NIN_audit/fixtures/fixtures.json').read_text())['results']
 expected=['NEP_Planted.matchAx','NEP_Planted.privateAx','NEP_Planted.proofAx','NEP_Planted.auxAx']
 require(len(fixtures)==8,'missing fidelity fixtures')
 for i,row in enumerate(fixtures):
  want=[expected[i]]if i<4 else []
  require(row['walked_axioms']==want and row['collect_axioms']==want and row['equal']is True,'fixture verdict changed')
 scan=[json.loads(l)for l in (E/'NIN_LOADED_scan.jsonl').read_text().splitlines()];validate_scan(scan)
 ledger=json.loads((E/'NIN_LEDGER_DELTA.json').read_text());validate_ledger(ledger)
 attempts=[json.loads(l)for l in (E/'NIN_ATTEMPTS.jsonl').read_text().splitlines()]
 require(len(attempts)<=60 and len({x['attempt']for x in attempts})==len(attempts),'attempt budget/uniqueness')
 for x in attempts:
  validate_admission(json.loads((E/(x['attempt']+'-admission.json')).read_text()))
  r=json.loads((E/x['attempt']/'receipt.json').read_text())
  require(r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},'scope caps changed')
  require(str(r['swaps'])=='0','swap used')
  for n,sha in r['source_hashes'].items():
   p=E/x['attempt']/'sources'/n
   require(p.is_file()and hashlib.sha256(p.read_bytes()).hexdigest()==sha,'source snapshot mismatch')
  require(bool(r['source_revision'])and bool(r['deps_fingerprint']['selected_objects']),'missing revision/dependency pins')
 # Source checks apply to final modules; retained failed source snapshots are excluded.
 for p in E.glob('NIN_*.lean'):
  code=re.sub(r'/\-.*?\-/','',p.read_text(),flags=re.S);code=re.sub(r'--[^\n]*','',code)
  require(not re.search(r'\b(sorry|axiom|admit|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats)',code),'forbidden proof escape')
  for name in re.findall(r'^theorem\s+(\w+)',code,re.M):require('#print axioms '+name in code,'missing top-theorem axiom print')
 require((E/'NIN_READONLY_NEP_WALKER.lean.txt').read_bytes()==(E.parent/'axaudit2-20261102/NEP_WALKER.lean').read_bytes(),'hardened walker changed')
 for p in E.rglob('*'):
  if p.is_file():require(p.stat().st_size<=20_000_000,'oversize evidence file')
 # Mutation denials exercise the SAME validators, without editing accepted receipts.
 controls=[]
 def denied(name,fn):
  try:fn()
  except AssertionError:controls.append(name);return
  raise AssertionError('mutation accepted: '+name)
 denied('missing-root',lambda:validate_roots(manifest['roots']+['NIN_Missing.root'],results))
 bad=copy.deepcopy(results);bad[0]['walked_axioms']=['sorryAx'];denied('nonstandard-raw-axiom',lambda:validate_roots(manifest['roots'],bad))
 bad=copy.deepcopy(scan);bad[0]['imports_match']=False;denied('missing-import-baseline',lambda:validate_scan(bad))
 bad=copy.deepcopy(scan);bad[0]['duplicate_owners']=[{'name':'NIN_bad'}];denied('incompatible-owner',lambda:validate_scan(bad))
 denied('allowed-false-even-exit0',lambda:validate_admission({'exit':0,'reservation':{'allowed':False}}))
 bad=copy.deepcopy(ledger);bad['row_promotions']=['TX1:137'];denied('row-promotion',lambda:validate_ledger(bad))
 out=dict(status='PASS',raw_roots=len(manifest['roots']),new_roots=len(manifest['new_roots']),raw_standard=True,summary_disagreements=disagreements,scan_modules=len(scan),scan_defects=0,fixture_count=8,mutation_denials=controls,attempts=len(attempts))
 (E/'NIN_VALIDATION.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(out))
if __name__=='__main__':main()
