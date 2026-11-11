#!/usr/bin/env python3
"""JSON RPC transport with bounded retries. Never opens wallet keys."""
import json,sys,time,urllib.request,urllib.error,base64,threading
_lock=threading.Lock()
_next_start=0.0
def pace(interval=.65):
    global _next_start
    with _lock:
        now=time.monotonic();delay=max(0,_next_start-now);_next_start=max(now,_next_start)+interval
    if delay:time.sleep(delay)

def rpc(url,method,params):
    for attempt in range(8):
        pace(.01 if url.startswith(("http://127.0.0.1:", "http://localhost:")) else .65)
        try:
            req=urllib.request.Request(url,json.dumps(dict(jsonrpc='2.0',id=1,method=method,params=params)).encode(),{'Content-Type':'application/json'})
            with urllib.request.urlopen(req,timeout=60) as r: v=json.load(r)
            if 'error' not in v:return v['result']
            if v['error'].get('code') not in (429,-32005):raise RuntimeError(v['error'])
        except (urllib.error.URLError,TimeoutError):
            if attempt==7:raise
        time.sleep(min(2**attempt,16))
    raise RuntimeError('RPC retry limit')
if __name__=='__main__':
    q=json.load(sys.stdin);print(json.dumps(rpc(q['url'],q['method'],q['params'])))
