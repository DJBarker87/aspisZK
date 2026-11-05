"""Additive Pool-consumer checks; the 599 verifier rows and historical predicates are untouched."""
from pathlib import Path
import json,re,hashlib,subprocess,sys
E=Path(__file__).resolve().parent;R=E.parents[1]
STANDARD={'propext','Classical.choice','Quot.sound'};FROZEN='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
LOCK='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
KMX='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
LIMITS={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
H=lambda b:hashlib.sha256(b).hexdigest()
def validate(overrides=None,final=False):
 overrides=overrides or {}
 def raw(n):return overrides[n] if n in overrides else (E/n).read_bytes()
 def js(n):return json.loads(raw(n))
 def txt(n):return raw(n).decode()
 attempts=[json.loads(l) for l in txt('NHC_ATTEMPTS.jsonl').splitlines()];ids=[x['attempt'] for x in attempts];assert len(ids)==len(set(ids))
 counts={'kani':sum(a.startswith('NHC_K') for a in ids),'lean':sum(a.startswith('NHC_L') for a in ids),'extract':sum(a.startswith('NHC_E') for a in ids)}
 assert counts['kani']<=120 and counts['lean']<=90 and counts['extract']<=2,counts
 for a in ids:
  rc=js(a+'/receipt.json');ad=js(a+'-admission.json');assert ad['exit']==0 and ad['reservation']['allowed'] is True,(a,'admission')
  assert rc['limits']==LIMITS and int(rc['swaps'])==0 and float(rc['wall_seconds'])>=0 and int(rc['peak_rss_kib'])>0,(a,'limits/metrics')
  assert rc['source_revision'] and rc['source_hashes'] and rc['command'],(a,'source/command pins')
  if a.startswith('NHC_K'):
   graph=js(a+'-graph-check.json');lock=js(a+'-lock-check.json');rule=js(a+'-rule16-check.json')
   assert graph['graph_matches_frozen'] and graph['exact_LPm_graph'] and not graph['added'] and not graph['edge_errors'],(a,'graph')
   assert lock==dict(before=LOCK,after=LOCK,unchanged=True),(a,'lock')
   assert rule['no_writable_static'] and not rule['violations'],(a,'writable static')
   assert js(a+'.json')['copy_patch_sha256']==KMX,(a,'copy patch')
 # The selected local theorem is paired to an actual-body Bool contract; every owner is generated.
 cert=js('NHC_LOADER_CERTIFICATE.json')
 assert cert['function']=='programs/aspis-pool/src/pair_forest_dispatch.rs::supported_loader' and cert['modifies']==[]
 assert cert['theorem']=='NHC_NGG_Loader.result' and cert['native_positive']=='NHC_K010' and cert['matched_control']=='NHC_K011'
 assert cert['domain']=='all 32-byte Pubkey owner values through a valid immutable Rust reference; no metadata, length, canonical-field, success or caller-output restriction'
 ref=R/cert['reference_source'];pins=json.loads((ref.parent/'NGG_EXTRACTION_PINS.json').read_text());assert H(ref.read_bytes())==cert['reference_sha256']==pins['reference_sha256']
 reference_line=next(l for l in ref.read_text().splitlines() if l.startswith('pub fn supported_loader('))
 positive=js('NHC_K010-shape.json')['source'];negative=js('NHC_K011-shape.json')['source']
 assert reference_line in positive and '#[kani::proof_for_contract(super::supported_loader)]' in positive
 assert positive.replace('\n r\n','\n !r\n')==negative and 'Pubkey::new_from_array(kani::any())' in positive
 assert 'VERIFICATION:- SUCCESSFUL' in txt('NHC_K010/stdout.log') and js('NHC_K010/receipt.json')['exit_status']==0
 assert 'VERIFICATION:- FAILED' in txt('NHC_K011/stdout.log') and 'Failed Checks: |r| *r == NHC_Loader::reference(owner)' in txt('NHC_K011/stdout.log')
 assert js('NHC_K011/receipt.json')['exit_status']!=0
 for a in ['NHC_K010','NHC_K011']:
  cfg=js(a+'.json');assert cfg['env']['CARGO_NET_OFFLINE']=='true' and cfg['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  assert cfg['program_features']=='r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit'
  assert '--harness-timeout' in cfg['native_command'] and cfg['native_command'][cfg['native_command'].index('--harness-timeout')+1]=='90s'
 source=subprocess.check_output(['git','show',FROZEN+':programs/aspis-pool/src/pair_forest_dispatch.rs'],cwd=R,text=True);a=source.index('fn supported_loader(');b=source.index('\n}',a)+2
 assert cert['frozen_body']==source[a:b] and cert['frozen_body_sha256']==H(source[a:b].encode())
 # Actual source statement/proof equality is checked against the deterministic retarget.
 prov=js('NHC_PROVENANCE.json');assert len(prov['files'])==27
 for row in prov['files']:
  p=row['target_module'].replace('.','/')+'.lean';assert H(raw(p))==row['target_sha256']
  snap=R/row['source_path'];assert H(snap.read_bytes())==row['source_sha256']
 ax=js('NHC_AUDIT.json');assert ax['standard_only'] and not ax['summary_disagreements']
 assert ax['scan']['dangling']==0 and ax['scan']['incompatible_owners']==0 and ax['scan']['import_mismatches']==0
 for row in map(json.loads,txt('NHC_LOADED_scan.jsonl').splitlines()):assert not row['dangling'] and not row.get('duplicate_owners') and row['imports_match']
 fx=js('NHC_audit/fixtures/fixtures.json')['results'];assert len(fx)==8
 for i,z in enumerate(fx):assert z['equal'] and (len(z['walked_axioms'])==1 if i<4 else z['walked_axioms']==[])
 walker=js('NHC_WALKER_PIN.json');assert walker['byte_identical'] and walker['sha256']==walker['reused_source_sha256']
 for mode in ['batch0','batch1']:
  proof='proof'+mode[-1];r=js('NHC_audit/'+mode+'/'+proof+'.json')
  for z in r['results']:assert set(z['walked_axioms'])<=STANDARD and z['equal']
 assert js('NHC_L053/receipt.json')['exit_status']==0
 assert all('sorryAx' not in l for l in js('NHC_L053/receipt.json')['print_axioms'])
 # Frozen shipped files are compared, not rebuilt: this job never edits them.
 assert subprocess.run(['git','diff','--quiet',FROZEN,'--','crates','programs','Cargo.lock'],cwd=R).returncode==0
 if final:
  assert not (E/'NHC_ACTIVE.json').exists() and not(E/'NHC_CLIENT_ACTIVE').exists()
  assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000]
 return dict(status='PASS',counts=counts,closed_candidate=cert['row'],scope='additive Pool-consumer checks; no verifier baseline change')
if __name__=='__main__':
 result=validate(final='--final' in sys.argv);(E/'NHC_VALIDATION.json').write_text(json.dumps(result,indent=1)+'\n');print(json.dumps(result))
