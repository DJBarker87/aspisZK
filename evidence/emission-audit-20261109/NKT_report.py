#!/usr/bin/env python3
"""Finalize audit-only row classifications and explicit coverage limitations."""
import collections,hashlib,json,lzma,pathlib,subprocess
P=pathlib.Path(__file__).parent

def main():
 a=json.load(open(P/'NKT_AUDIT.json'));rr=json.load(open(P/'NKT_ROOT_REACHABILITY.json'));byroot={x['root']:x for x in rr}
 d=json.loads(lzma.open(P.parent/'ledger19-20261108/NKN_LEDGER.json.xz').read())
 controls=json.load(open(P/'NKT_CHECKER_CONTROLS.json'));assert all(x['pass'] for x in controls.values());a['controls']=controls
 out=['# NKT row impact','', 'Target not yet established. No ledger edits. These classifications concern the confirmed three batch_tree exit losses only; unresolved source/tool provenance prevents a universal clean bill.','', 'Already OPEN control rows: TX1:083 and TX2:055, batch_tree, exits candidate.rs:196/200/203. No admitted exact-Result theorem is listed in ledger19. Retain OPEN; native Err/prefix transport required by (bb)/(bc). No new REOPEN is requested.','', 'CLOSED rows and pending candidates (INSENSITIVE means their relevant Result does not consume the confirmed lost exits):','']
 impact=[]
 for r in d['rows']:
  if r['status']!='CLOSED':continue
  roots=[z['root'] for z in r['root_owners']]
  assert all(z in byroot and byroot[z]['reachable_receipts'] for z in roots)
  special=[z for z in roots if byroot[z]['batch_tree_dependencies']]
  if not roots:
   assert r['row'] in ['TX1:059','TX2:040'] and not r['canonical_callees']
   why='Frozen WideExact::to_limbs returns its eight stored u32 coordinates, with no loop or callees (wide_exact.rs:238-249). Ledger19 names no theorem/root for this row; root-provenance gap NKT-F3, not a newly validated credit.'
  elif r['row']=='TX1:186':
   why='NHS_CheckpointPacket.source concludes preparation/query/flush/writer facts; batch dependency is structural configuration, not a consumed rejected batch Result. NKT_FINDINGS.md row-impact section; NHS_CheckpointPacket.lean:11.'
  elif r['row'] in ['TX1:168','TX1:169','TX1:170']:
   why='Independent helper roots exclude batch_tree; additional RPx_Deployed.deployed is conditional on extraction and native accepted runs, not an unconditional rejected-batch Result law. Helper claim only; headline fidelity remains OPEN. NKT_FINDINGS.md.'
  else:
   assert not special,(r['row'],special)
   why='No batch_tree constant in any checked root closure; NKT_ROOT_REACHABILITY.json.'
  rec={'row':r['row'],'function':r['function'],'status':r['status'],'classification':'INSENSITIVE','exit':'candidate.rs:196/200/203','exact_theorems':roots,'citation':why,'batch_tree_in_root_closure':special}
  impact.append(rec);out.append('- '+r['row']+' | '+r['function']+' | exits196/200/203 | INSENSITIVE | '+', '.join(roots)+' | '+why)
 for packet in a['pending_inputs']:
  for f in packet['data'].get('functions',[]):
   roots=f.get('roots',f.get('lean_roots',[]));ids=f.get('rows',[f.get('row')])
   assert all(z in byroot and byroot[z]['reachable_receipts'] and not byroot[z]['batch_tree_dependencies'] for z in roots)
   for row in ids:
    rec={'row':row,'function':f['function'],'status':'PENDING','classification':'INSENSITIVE','exit':'candidate.rs:196/200/203','exact_theorems':roots,'citation':packet['path']+'; NKT_ROOT_REACHABILITY.json; canonical scanner additionally NKL_ScanModel.source width57607'}
    impact.append(rec);out.append('- '+str(row)+' (PENDING) | '+f['function']+' | exits196/200/203 | INSENSITIVE | '+', '.join(roots)+' | '+rec['citation'])
 (P/'NKT_AFFECTED_ROWS.md').write_text('\n'.join(out)+'\n');(P/'NKT_ROW_IMPACT.json').write_text(json.dumps(impact,indent=1)+'\n')
 a['impact_summary'].update({'closed_rows_reviewed':sum(r['status']=='CLOSED' for r in d['rows']),'checked_roots':len(rr),'roots_with_reachability_receipt':sum(bool(r['reachable_receipts']) for r in rr),'new_reopen_recommendations':[], 'manual_structural_root_cases':['AspisR1.NHS_CheckpointPacket.source','AspisR1.RPx_Deployed.deployed'],'classification_scope':'known batch_tree exits only; no corpus-wide fidelity certification','closed_rows_without_named_root':['TX1:059','TX2:040'],'complete_audit':False})
 prov=json.load(open(P/'NKT_EXTRACTIONS.json'));a['extraction_provenance_summary']=dict(collections.Counter(x['origin_status'] for x in prov));a['extraction_provenance_artifact']='NKT_EXTRACTIONS.json'
 a['remaining_obligations']=[{'member':'exact selected source inventory','status':'OPEN','reason':'Filename resolution is conservative; recorded imports/object manifests are pinned but many selected objects lack adjacent retained source. Host recovery found three sources. Need exact archived source-to-object mapping; a print/reachability proof cannot recover historical source provenance.'},{'member':'tool origin for each emission','status':'OPEN','count':sum(x['origin_status']=='UNRESOLVED_TOOL_ORIGIN' for x in prov),'reason':'Recover raw-emission/tool receipts for these historical/derived blobs. No binary pin is inferred from a name. New Charon or Lean inspection does not reconstruct historical Aeneas provenance; new Aeneas allowance is zero.'},{'member':'reference/library/native source associations','status':'OPEN','count':sum(x['frozen_body_sha256'] is None for x in a['functions']),'reason':'Null frozen hashes are explicit references, closures, constants, libraries or unresolved mappings; they do not certify a native body. Resolve at exact selected-source mapping, without new row proofs.'}]
 for f in a['functions']:
  if f.get('frozen_body_sha256'):f['frozen_body_mapping_status']='same-name/location candidate in frozen source; source owner identity is not certified by hashing'
 a['validation_status']='PATTERN_CONTROLS_AND_ROOT_TRIAGE_PASS_WITH_PROVENANCE_GAPS';(P/'NKT_AUDIT.json').write_text(json.dumps(a,separators=(',',':'))+'\n')
 pins=[]
 for f in P.iterdir():
  if f.is_file() and f.name not in ['NKT_INPUT_PINS.json','NKT_ATTEMPTS.jsonl','NKT_report.log'] and not f.name.startswith('NKT_FINAL_VALIDATION'):
   pins.append({'path':str(f),'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'bytes':f.stat().st_size})
 (P/'NKT_INPUT_PINS.json').write_text(json.dumps({'audit_revision':a['audit_revision'],'frozen_revision':a['frozen_revision'],'files':pins},indent=1)+'\n')
 print(json.dumps({'closed_rows':a['impact_summary']['closed_rows_reviewed'],'pending_occurrences':len(impact)-a['impact_summary']['closed_rows_reviewed'],'checked_roots':len(rr),'new_reopens':0,'universal_audit_complete':False}))
if __name__=='__main__':main()
