from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent
attempt,module=sys.argv[1:3]
env=json.loads((E/'NLL_ENV.json').read_text())
cfg=dict(attempt=attempt,kind='lean',module=module,sources=[module+'.lean'],upload=[module+'.lean'],command=[env['LEAN_SYSROOT']+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-o','NLL_objects/'+module+'.olean',module+'.lean'],collect=[],timeout=180,env=env)
(E/(attempt+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
