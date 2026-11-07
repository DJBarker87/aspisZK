from NMX_formal import *
env=json.loads((E/'NMX_R3_ENV.json').read_text());records=json.loads((E/'NMX_REV3_CANONICAL.json').read_text());done={x['module'] for x in records if x['exit_status']==0}
base=E.parent/'rowspec-lead-20261107';names={p.stem:p for p in base.glob('RSL_*.lean') if p.stem!='RSL_Audit'}
order=[]
def visit(m):
 if m in done or m in order:return
 for d in re.findall(r'^import (RSL_\w+)',names[m].read_text(),re.M):visit(d)
 order.append(m)
for m in names:visit(m)
for n,m in enumerate(order,895):
 p=names[m];text=p.read_text();src='NMX_R3_canonical/'+m+'.lean'
 r=run('NMX_L'+str(n),'inspect',m,command=[env['LEAN_SYSROOT']+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NMX_R3_canonical','-o','NMX_R3_canonical_objects/'+m+'.olean',src],extra={src:text},env_extra=env)
 records.append(dict(module=m,source=str(p.relative_to(E.parent.parent)),source_sha256=sha(text.encode()),attempt=r['attempt'],exit_status=r['exit_status']));(E/'NMX_REV3_CANONICAL.json').write_text(json.dumps(records,indent=1)+'\n')
 assert r['exit_status']==0
print('All relevant original RSL owners now revision3; no library import can resolve a rev2 RSL object')
