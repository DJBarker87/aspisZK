import json,sys
d=json.load(open(sys.argv[1]));t=d['translated']
f=[f for f in t['fun_decls'] if f and 'decode_lane_from_pool_release' in json.dumps(f.get('item_meta',{}).get('name'))][0]
b=f['body'];body=b['Structured'] if 'Structured' in b else b
def kind(s):
    k=s['kind'];return k if isinstance(k,str) else list(k)[0]
def blocks_of(s):
    k=s['kind']
    if isinstance(k,str):return []
    n=list(k)[0];v=k[n];res=[]
    def walk(o):
        if isinstance(o,dict):
            if 'statements' in o:res.append(o);return
            for x in o.values():walk(x)
        elif isinstance(o,list):
            for x in o:walk(x)
    walk(v);return res
def find(blk,path):
    for i,s in enumerate(blk['statements']):
        if kind(s)=='Loop':
            print('PATH',path,'| loop at index',i,'of',len(blk['statements']))
            print('AFTER (kinds):',[kind(x) for x in blk['statements'][i+1:]])
            lb=blocks_of(s)[0]
            def cnt(o,name):
                c=0
                if isinstance(o,dict):
                    if o.get('kind')==name or (isinstance(o.get('kind'),dict) and name in o['kind']):c+=1
                    for v in o.values():c+=cnt(v,name)
                elif isinstance(o,list):
                    for v in o:c+=cnt(v,name)
                return c
            print('loop body: Break',cnt(lb,'Break'),'Return',cnt(lb,'Return'),'Continue',cnt(lb,'Continue'))
        for sub in blocks_of(s):find(sub,path+[kind(s)])
find(body['body'],[])
