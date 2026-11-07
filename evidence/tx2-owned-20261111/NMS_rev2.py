from NMS_formal import *
mods=['RSL_Base','RSL_Pool','RSL_TX2_217','RSL_TX2_234','RSL_TX2_233','RSL_TX2_242','RSL_TX2_241']
if __name__=='__main__':
 env=json.loads((E/'NMS_ENV.json').read_text())
 root=B+'/NMS_R2_RSL_objects'
 env['LEAN_PATH']=root+':'+env['LEAN_PATH']
 (E/'NMS_ENV.json').write_text(json.dumps(env,indent=1)+'\n')
 for i,m in enumerate(mods,282):
  src='NMS_R2_RSL_sources/'+m+'.lean'
  cmd=[env['LEAN_SYSROOT']+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NMS_R2_RSL_sources','-o','NMS_R2_RSL_objects/'+m+'.olean',src]
  rc=run(f'NMS_L{i:03}','support','NMS_rev2_'+m,cmd,{src:(E.parent/'rowspec-lead-20261107'/(m+'.lean')).read_text(),'NMS_R2_RSL_objects/.keep':''})
  assert rc['exit_status']==0,(m,rc['exit_status'])
