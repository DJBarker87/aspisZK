if __name__ == '__main__':
    raise SystemExit('SbfFinite SOURCE ONLY: public entry disabled before imports')
"""Pure fixed finite schema and exact input binding; no host approval claim."""
import hashlib
import json
from SbfFiniteLinux_capture import require, canonical
from SbfFinite_fixed import SCHEMA, RUNTIME, CATALOG, ROOT, ARGV, ENV

def pin(raw):return dict(size=len(raw),sha256=hashlib.sha256(raw).hexdigest())

def validate(value):
    require(type(value) is dict and set(value)=={'schema','runtime'} and value['schema']==SCHEMA,'finite schema')
    m=value['runtime']
    require(type(m) is dict and set(m)=={'version','root','uid','gid','argv','env','files'},'runtime schema')
    require(m['version']=='SbfFiniteLinux-tiny-v1' and m['root']==ROOT,'fixed version/root')
    require(type(m['uid']) is int and type(m['gid']) is int and m['uid']==m['gid']==1000,'fixed guest IDs')
    require(m['argv']==list(ARGV) and m['env']==ENV,'captured postexec argv/body/environment')
    rows=m['files'];require(type(rows) is list and len(rows)==92<=256,'exact92 rows')
    seen=set();total=0
    for r in rows:
        require(type(r) is dict and set(r)=={'logical','physical','size','sha256','mode'},'row schema')
        canonical(r['logical']);canonical(r['physical'])
        require(r['logical'] not in seen,'duplicate guest path');seen.add(r['logical'])
        require(r['physical']==ROOT+r['logical'],'fixed new-copy destination')
        require(type(r['size']) is int and 0<=r['size']<=16*2**20,'file size bound')
        require(r['mode'] in (0o444,0o555),'file mode')
        require(type(r['sha256']) is str and len(r['sha256'])==64 and all(c in '0123456789abcdef' for c in r['sha256']),'hash syntax')
        total+=r['size']
    require(total==35655597<=64*2**20,'alias copies total bound')
    require(m==RUNTIME,'literal reviewed finite candidate equality')
    return m

def validate_fixed():
    m=validate(dict(schema=SCHEMA,runtime=RUNTIME))
    require(len(CATALOG)==92 and len({r['source']['physical'] for r in CATALOG})==82,'physical accounting')
    for r,c in zip(m['files'],CATALOG):
        require(c['guest']==r['logical'] and c['destination']==r['physical'] and
                c['source']['size']==r['size'] and c['source']['sha256']==r['sha256'] and c['mode']==r['mode'],'catalog exact binding')
    return m
