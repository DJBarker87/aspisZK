import json,glob,hashlib,os
rows=[]
for r in sorted(glob.glob('PCVD_L[0-9][0-9][0-9]/receipt.json')):
    d=json.load(open(r)); L=d['attempt']
    for f,h in d['source_hashes'].items():
        name=os.path.basename(f)
        cur=hashlib.sha256(open(name,'rb').read()).hexdigest() if os.path.exists(name) else None
        rows.append((L,name,d['exit_status'],round(d['wall_seconds'],1),d['peak_rss_kib'],d['swaps'],'MATCH' if cur==h else ('MISSING' if cur is None else 'CHANGED')))
for x in rows: print(*x)
