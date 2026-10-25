"""Bounded JSON policy preflight. No Lean invocation or kernel-PASS output."""
import json,os,pathlib,stat
MAX_JSON=16*1024*1024
class Reject(ValueError): pass

def exact_name(x,depth=0):
    if depth>256 or not isinstance(x,list): raise Reject('invalid Name depth/shape')
    if x==['anon']: return ('anon',)
    if len(x)!=3 or x[0] not in ('str','num') or not isinstance(x[2],str):
        raise Reject('invalid exact Name constructor')
    p=exact_name(x[1],depth+1)
    if x[0]=='num' and (not x[2].isascii() or not x[2].isdigit() or str(int(x[2]))!=x[2]):
        raise Reject('noncanonical Name.num')
    return (x[0],p,x[2])

def encode_name(x):
    if x==('anon',): return ['anon']
    return [x[0],encode_name(x[1]),x[2]]

def str_name(*segments):
    n=['anon']
    for segment in segments:n=['str',n,segment]
    return n

def bounded_json(path):
    p=pathlib.Path(path)
    # Check every path component before opening: reject directory/file symlinks.
    for a in reversed([p,*p.parents]):
        if stat.S_ISLNK(a.lstat().st_mode): raise Reject('symlink component')
    if not stat.S_ISREG(p.lstat().st_mode) or p.stat().st_size>MAX_JSON:
        raise Reject('not bounded regular JSON')
    fd=os.open(p,os.O_RDONLY|os.O_NOFOLLOW)
    with os.fdopen(fd) as f:return json.load(f)

def policy(data):
    if data.get('schema')!='Port30JOIN-exact-selection-v1': raise Reject('schema')
    if data.get('kernel_enabled') is not False: raise Reject('kernel must stay disabled')
    if data.get('base_import')!='Lean': raise Reject('project trust import forbidden')
    if data.get('actual_name_reader') is not True: raise Reject('printed names forbidden')
    if data.get('closure_complete') is not True: raise Reject('missing full closure')
    if data.get('groups_complete') is not True: raise Reject('missing complete groups')
    # These are future evidence references, NOT validation of their truth in Python.
    for k in ('sysroot_pins','raw_byte_pins','strict_v3_receipt'):
        if not data.get(k):raise Reject('missing '+k)
    seen=set();names=set()
    for row in data.get('choices',[]):
        n=exact_name(row['name'])
        if n in names:raise Reject('duplicate Name choice')
        names.add(n)
        if row.get('mode') not in ('literal','recheck-current'): raise Reject('variant mode')
        if row.get('mode')=='recheck-current' and not row.get('review_reason'):
            raise Reject('re-pin needs explicit reason')
        variants=row.get('variants',[])
        if not variants:raise Reject('missing variants')
        for v in variants:
            ident=(n,v['origin'])
            if ident in seen:raise Reject('duplicate origin')
            seen.add(ident)
            if v.get('kind')=='axiom' or v.get('unsafe') or v.get('partial'):
                # Unsafe variants may remain data, but cannot be selected logical terms.
                if v['origin']==row.get('chosen_origin'): raise Reject('inadmissible selected seed')
        if row.get('chosen_origin') not in [v['origin'] for v in variants]:raise Reject('chosen origin absent')
        if row['mode']=='literal' and row.get('complete_strict_v3_all_variants') is not True:
            raise Reject('literal mode needs complete representation comparison')
    for seed in data.get('seeds',[]):
        if exact_name(seed) not in names:raise Reject('seed has no explicit choice')
    return {'status':'policy-shape-only; kernel disabled; not verified closure/equality',
            'choices':len(names),'seeds':len(data.get('seeds',[]))}

if __name__=='__main__':
    import sys
    try: print(json.dumps(policy(bounded_json(sys.argv[1]))))
    except (Reject,KeyError,ValueError,OSError) as e:
        print(json.dumps({'status':'REJECT','reason':str(e)}));sys.exit(1)
