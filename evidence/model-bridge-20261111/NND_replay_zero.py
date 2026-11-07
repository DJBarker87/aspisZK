from NND_formal import *
manifest=json.loads((E/'NND_ZERO_REUSE.json').read_text());n=91;skips=[]
for row in manifest['order']:
 module=row['module'];txt=(E/row['path']).read_text();h=sha(txt.encode())
 prior=[json.loads(l) for l in (E/'NND_ATTEMPTS.jsonl').read_text().splitlines()]
 found=next((x for x in prior if x.get('module')==module and x.get('exit_status')==0 and h in x.get('source_hashes',{}).values()),None)
 if found:skips.append(dict(module=module,attempt=found['attempt'],sha256=h));continue
 src='NND_replay/'+module.replace('.','/')+'.lean';env=json.loads((E/'NND_ENV.json').read_text())['env']
 cmd=[env['LEAN_SYSROOT']+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NND_replay','-o','NND_objects/'+module.replace('.','/')+'.olean',src]
 r=run(f'NND_L{n:03}','support',module,cmd,extra={src:txt});n+=1
 if r['exit_status']:raise SystemExit(r['exit_status'])
(E/'NND_ZERO_REUSE_SKIPS.json').write_text(json.dumps(skips,indent=1)+'\n')
print(json.dumps(dict(next_attempt=n,skips=skips)))
