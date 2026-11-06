from pathlib import Path
import json,subprocess,lzma,hashlib
E=Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest()
def read(path):return subprocess.check_output(['git','show','HEAD:'+path])
def j(path):return json.loads(read(path))
checks=[]
for folder,pre,pairs in [('verify-observed5-20261107','NIX',[(49,50),(73,74),(75,76)]),('verify-observed6-20261107','NJG',[(16,17),(18,19)])]:
 for pos,neg in pairs:
  pair=[]
  for n in[pos,neg]:
   a=f'{pre}_K{n:03}';base='evidence/'+folder+'/';rp=base+a+'/receipt.json';r=j(rp);g=j(base+a+'-graph-check.json');l=j(base+a+'-lock-check.json')
   try:raw=read(base+a+'/stdout.log')
   except subprocess.CalledProcessError:raw=lzma.decompress(read(base+a+'/stdout.log.xz'))
   log=raw.decode();expected=0 if n==pos else 1
   assert r['exit_status']==expected and ('VERIFICATION:- SUCCESSFUL'in log if expected==0 else 'VERIFICATION:- FAILED'in log),a
   assert g['graph_matches_frozen']and not g['edge_errors']and l['unchanged']and l['before']==l['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
   pair.append(dict(attempt=a,exit=expected,receipt_path=rp,receipt_sha256=H(read(rp)),graph=g,lock=l,source_hashes=r['source_hashes'],revision=r['source_revision']))
  diff=[k for k in set(pair[0]['source_hashes'])|set(pair[1]['source_hashes'])if pair[0]['source_hashes'].get(k)!=pair[1]['source_hashes'].get(k)];assert not diff,(pre,pos,diff)
  checks.append(dict(positive=pair[0],negative=pair[1],common_input_differences=diff))
(E/'NJW_NJM_INHERITED_NATIVE.json').write_text(json.dumps(dict(status='PASS',pairs=checks,new_runs=0,inventory='NJM_CUTS.md: NIX round Args/post and dispatch; NJG K016–019 exact native rounds Cut under(ai)(5). These are reviewed native transcriptions, not extra game hypotheses.'),indent=1)+'\n')
print(json.dumps(dict(stage='inherited_native',pairs=len(checks),status='PASS')))
