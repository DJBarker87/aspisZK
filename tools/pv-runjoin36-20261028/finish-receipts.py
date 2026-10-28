from pathlib import Path
import json,hashlib,lzma,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin36-20261028';sha=lambda b:hashlib.sha256(b).hexdigest();features=json.load(open(E/'deployed-feature-graph.json'))
for phase in ['metadata','charon','aeneas','charon-narrow','aeneas-narrow']:
 p=E/phase/'receipt.json';x=json.load(open(p));x['resolved_deployed_features']=features;x['resolved_deployed_features_sha256']=sha((E/'deployed-feature-graph.json').read_bytes());x['toolchain_versions_receipt']='toolchains-and-initial-llbc.txt';x['input_manifest_sha256']=sha((E/'input-source-pins.json').read_bytes());x['source_revision_note']='Input frozen at entry 1135ec947f; exact source hashes in input-source-pins.json';p.write_text(json.dumps(x,indent=2)+'\n')
for leaf in ['SelectedMask.llbc','SelectedMask-narrow.llbc']:
 p=E/(leaf+'.xz');b=lzma.decompress(p.read_bytes());(E/(leaf+'.sha256')).write_text(sha(b)+'  '+leaf+'\n')
head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();base='1135ec947f86a1d3e375092b9f99e3b5db6fc164'
checks={}
for label,paths in [('shipped',['crates','programs','tools/r1-cost-probe']),('endpoint',['docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineDeployedReal.lean']),('ledger',['docs/research/100bit-spend-path-20261013/design/PRIVACY-LEDGER-20261026.md'])]:
 r=subprocess.run(['git','diff',base,head,'--',*paths],capture_output=True,text=True);checks[label]=dict(command=r.args,exit=r.returncode,output=r.stdout,stderr=r.stderr);assert r.returncode==0 and not r.stdout
(E/'boundaries-unchanged.json').write_text(json.dumps(checks,indent=2)+'\n')
metrics=[]
for phase in ['metadata','charon','aeneas','charon-narrow','aeneas-narrow']:
 x=json.load(open(E/phase/'receipt.json'));metrics.append(dict(phase=phase,exit=x['exit'],wall_seconds=x['wall_seconds'],peak_rss_bytes=max(x['peak_aggregate_rss_bytes'],x['peak_child_rss_bytes']),swaps=x['swaps'],source_revision=x['source_revision'],axioms=x['axioms']))
(E/'metrics.json').write_text(json.dumps(metrics,indent=2)+'\n');print(json.dumps(metrics,indent=2))
