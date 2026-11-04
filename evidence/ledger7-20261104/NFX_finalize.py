"""Verify new raw graphs, trusted walker fixtures and one combined import scan."""
from pathlib import Path
import json,hashlib,lzma,re,subprocess,collections
E=Path(__file__).resolve().parent;R=E.parents[1];std={'propext','Classical.choice','Quot.sound'}
J=lambda p:json.loads((E/p).read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def need(v,m):
 if not v:raise ValueError(m)
def build():
 manifest=J('NFX_AUDIT_ROOTS.json');expected=set(manifest['roots']);results=[];children=[];binary=None
 for batch in range((len(manifest['groups'])+9)//10):
  attempt=f'NFX_L{27+batch:03}';parent=J(attempt+'/receipt.json');need(parent['exit_status']==0,'failed audit '+attempt)
  pin=J(attempt+'/NFX_ProofDriver_BINARY_PIN.json')['sha256']
  if binary is None:binary=pin
  need(binary==pin,'raw driver changed between batches')
  for p in sorted((E/'NFX_audit'/('batch'+str(batch))).glob('*.json')):
   child=json.loads(p.read_text());need(child['exit_status']==0 and child['swaps']=='0','child failed/swapped')
   child.update(source_revision=parent['source_revision'],source_sha256=parent['source_hashes'],parent_attempt=attempt)
   children.append(child)
   for row in child['results']:
    need(set(row['walked_axioms'])<=std,'nonstandard raw axiom')
    need(row['root'] in expected,'unselected audit root')
    name='NFX_NEP_'+p.stem+'_'+row['root']+'_REACHABLE.txt'
    archive=E/(name+'.xz');raw=lzma.decompress(archive.read_bytes())
    need(hashlib.sha256(raw).hexdigest()==(E/(name+'.sha256')).read_text().strip(),'raw graph digest')
    row.update(mode=p.stem,graph_archive=archive.name,compressed_sha256=sha(archive),uncompressed_sha256=hashlib.sha256(raw).hexdigest(),parent_attempt=attempt)
    results.append(row)
 need(len(results)==len(expected) and {r['root'] for r in results}==expected,'omitted or duplicate roots')
 fixtures=J('NFX_audit/fixtures/fixtures.json');need(fixtures['exit_status']==0,'fixture process failed')
 import sys
 sys.path.insert(0,str(R/'evidence/ledger6-20261104'));import NFK_validate
 NFK_validate.fixtures(fixtures['results'])
 need(J('NFX_L026/NFX_ProofDriver_BINARY_PIN.json')['sha256']==binary,'fixture/final driver mismatch')
 scan_number=27+(len(manifest['groups'])+9)//10;scan_attempt='NFX_L035'
 sr=J(scan_attempt+'/receipt.json');need(sr['exit_status']==0,'scan process failed')
 scan=[json.loads(l) for l in (E/'NFX_LOADED_scan.jsonl').read_text().splitlines()]
 failures=[r for r in scan if r['dangling'] or r['duplicate_owners'] or not r['imports_match']]
 need(not failures,'incoherent import: '+str([(r['module'],len(r['dangling']),len(r['duplicate_owners']),r['imports_match']) for r in failures][:30]))
 legacy=[r['module'] for r in map(json.loads,(E/'NFX_audit/inventory-s/inventory-s.log').read_text().splitlines()) if r['dangling']]
 # A module name is not an object identity. The canonical RPx closure reuses
 # two unchanged common libraries, rebuilds twelve, and excludes the old entry.
 forbidden={'S1SemanticPhaseV1','PreparedFromQmSourceBridge','NFD_FinalAudit','NFH_FinalAudit','NFJ_Scanner','NEM_ValidatorComposed','NEQ_EncoderOracle','NEU_ReconstructAdopted','NEX_PublicModel','NEY_EmitComposed','NFD_RequestOracle','ExtractedTx1Reachability'}
 loaded={r['module'] for r in scan};need(not(forbidden&loaded),'legacy packet/owner forest imported')
 variants=J('NFX_LEGACY_FAMILY_PINS.json');common={'FS2.DuplexDecodes','S2X_SecondCut'}
 for v in variants:
  if v['module'] not in loaded:continue
  same=sorted(v['legacy']['files'].values())==sorted(v['final']['files'].values())
  need(same==(v['module'] in common),'unexpected legacy object variant '+v['module'])
 # All 650 old unresolved edges are absent as unresolved edges in the full
 # authoritative environment. Common library reuse is disclosed, not hidden.

 proof=(E/'NFX_ProofDriver.lean').read_text();up=(R/'evidence/slice-q-accum-20261104/NFS_ProofDriver.lean').read_text();baseline=(R/'evidence/axaudit2-20261102/NEP_Driver.lean').read_text()
 need(proof[:proof.index('unsafe def main')]==up[:up.index('unsafe def main')],'pre-runtime prefix changed')
 action=lambda s:s[s.index('  let ctx : Command.Context'):]
 need(action(proof)==action(baseline),'NEP raw audit action changed')
 scan_source=(E/'NFX_Driver.lean').read_text();prior_scan=(R/'evidence/slice-q-accum-20261104/NFS_Driver.lean').read_text()
 need(scan_source[:scan_source.index('unsafe def main')]==prior_scan[:prior_scan.index('unsafe def main')],'incoherence scanner core changed')
 need((R/'evidence/slice-q-mul4-20261104/NFA_WALKER.lean').read_bytes()==(R/'evidence/axaudit2-20261102/NEP_WALKER.lean').read_bytes(),'walker source changed')
 # The imported compiled walker and Aeneas objects are pinned in every parent
 # receipt, and the same walker C is used for fixtures and all final roots.
 receipts=[]
 for p in sorted(E.glob('NFX_L*/receipt.json')):
  r=json.loads(p.read_text());a=r['attempt'];ad=J(a+'-admission.json')
  need(ad['exit']==0 and ad['reservation']['allowed'] is True,'unadmitted scope')
  need(r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},'resource cap drift')
  need(r['swaps']=='0','swapped scope')
  for key in ['module','command','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','print_axioms']:need(key in r,'missing section6 field '+key)
  receipts.append(dict(attempt=a,target=r['module'],command=r['command'],exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],source_revision=r['source_revision'],source_hashes=r['source_hashes'],print_axioms=r['print_axioms']))
 for module,a in [('NFX_COMBINED_IMPORT','NFX_L022'),('NFX_ProofDriver','NFX_L023'),('NFX_Driver','NFX_L021')]:
  r=J(a+'/receipt.json');need(r['exit_status']==0 and sha(E/(module+'.lean'))==r['source_hashes']['NFX_generated/'+module+'.lean'],'current source not compiled '+module)
 out=dict(status='PASS_COHERENT_ADMITTED_FOREST_WITH_QUALIFICATIONS',headline='AspisR1.RPx_Deployed.deployed',combined_import='NFX_COMBINED_IMPORT.lean',combined_source_sha256=sha(E/'NFX_COMBINED_IMPORT.lean'),root_count=len(results),results=results,fixtures=fixtures['results'],driver_binary_sha256=binary,walker_sha256=sha(R/'evidence/axaudit2-20261102/NEP_WALKER.lean'),walker_byte_identical=True,NEP_raw_action_byte_identical=True,raw_walk_authoritative=True,standard_axioms_only=True,collect_disagreements=[r['root'] for r in results if not r['equal']],scan=dict(modules=len(scan),dangling=0,duplicate_owners=0,import_mismatches=0,cached_theorem_replicas=sum(len(r['cached_replicas']) for r in scan),output_sha256=sha(E/'NFX_LOADED_scan.jsonl'),receipt=scan_attempt+'/receipt.json'),legacy_forest=dict(admitted=False,inherited_dangling_references=650,inherited_bad_modules=legacy,forbidden_packet_owners=sorted(forbidden),all_forbidden_packet_owners_absent=True,shared_library_names=sorted(set(legacy)&loaded),byte_identical_shared_libraries=sorted(common),object_variant_pins='NFX_LEGACY_FAMILY_PINS.json',source_inventory='NFX_audit/inventory-s/inventory-s.log',qualified_direct_rows=len(J('NFX_COHERENCE_DENIALS.json')),failed_headline_import='NFX_L008/receipt.json'),parent_receipts=receipts,child_receipts=children,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),cold_release_replay=False,security_target_established=False,new_theorems=0,kani_runs=0,extraction_runs=0)
 return out
if __name__=='__main__':
 out=build();(E/'NFX_AUDIT.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps({k:out[k] for k in ['status','root_count','scan','collect_disagreements']}))
