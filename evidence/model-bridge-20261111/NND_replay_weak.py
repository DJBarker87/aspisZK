from NND_formal import *
names=['NNC_SourceCuts','NNC_ByteCarriers','NNC_CommonWeak','NNC_ResumeHeader','NNC_064Weak','NNC_WeakSpec']
for i,n in enumerate(names,76):
 src='NND_replay/'+n+'.lean'
 env=json.loads((E/'NND_ENV.json').read_text())['env']
 cmd=[env['LEAN_SYSROOT']+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NND_replay','-o','NND_objects/'+n+'.olean',src]
 r=run(f'NND_L{i:03}','support',n,cmd,extra={src:(E/'NND_reuse'/(n+'.lean')).read_text()})
 if r['exit_status']:raise SystemExit(r['exit_status'])
