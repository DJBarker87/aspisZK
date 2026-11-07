from NMX_formal import *
mods=['RSL_Base','RSL_Pool','RSL_TX2_217','RSL_TX2_234','RSL_TX2_233']
env=json.loads((E/'NMX_ENV.json').read_text());env['LEAN_PATH']=B+'/NMX_R2_canonical_objects:'+env['LEAN_PATH']
(E/'NMX_REV2_ENV.json').write_text(json.dumps(env,indent=1)+'\n')
r=ssh('python3',f"from pathlib import Path; Path({(B+'/NMX_R2_canonical_objects')!r}).mkdir(exist_ok=True)");assert r.returncode==0,r.stderr
records=[]
for i,m in enumerate(mods):
 p=E.parent/'rowspec-lead-20261107'/(m+'.lean');s=p.read_text();src='NMX_R2_canonical/'+m+'.lean'
 r=run('NMX_L'+str(483+i),'inspect',m,[env['LEAN_SYSROOT']+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NMX_R2_canonical','-o','NMX_R2_canonical_objects/'+m+'.olean',src],{src:s},env_extra=env)
 records.append(dict(module=m,source=str(p.relative_to(E.parent.parent)),source_sha256=sha(s.encode()),attempt=r['attempt'],exit_status=r['exit_status']))
 (E/'NMX_REV2_CANONICAL.json').write_text(json.dumps(records,indent=1)+'\n')
 if r['exit_status']:raise RuntimeError('STOP canonical predecessor failed')
