from NMX_formal import *
env=json.loads((E/'NMX_R3_ENV.json').read_text())
r=ssh('python3',f"from pathlib import Path; Path({(B+'/NMX_R3_canonical_objects')!r}).mkdir(exist_ok=True)");assert r.returncode==0,r.stderr
records=[]
for i,m in enumerate(['RSL_Base','RSL_Pool','RSL_TX2_217','RSL_TX2_234','RSL_TX2_233']):
 p=E.parent/'rowspec-lead-20261107'/(m+'.lean');s=p.read_text();src='NMX_R3_canonical/'+m+'.lean'
 r=run('NMX_L'+str(661+i),'inspect',m,[env['LEAN_SYSROOT']+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NMX_R3_canonical','-o','NMX_R3_canonical_objects/'+m+'.olean',src],{src:s},env_extra=env)
 records.append(dict(module=m,source=str(p.relative_to(E.parent.parent)),source_sha256=sha(s.encode()),attempt=r['attempt'],exit_status=r['exit_status']))
 (E/'NMX_REV3_CANONICAL.json').write_text(json.dumps(records,indent=1)+'\n')
 if r['exit_status']:raise RuntimeError('STOP canonical predecessor failed')
