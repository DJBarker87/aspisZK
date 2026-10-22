#!/usr/bin/env python3
"""Trace frozen LLVM indirect operands through direct-call formal arguments.
Unsupported SSA/memory flows remain OPEN; address-taken sets are not targets.
"""
import collections,hashlib,json,re
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-s10-inventory5-20261021')
P=H.parent/'codex-cx-s10-inventory3-20261021'
F=H.parent/'codex-cx-s10-inventory2-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def parts(s):
    out=[];start=0;stack=[];quoted=False
    for i,c in enumerate(s):
        if c=='"':quoted=not quoted
        if quoted:continue
        if c in '([{<':stack.append(c)
        elif c in ')]}>':
            if stack:stack.pop()
        elif c==',' and not stack:out.append(s[start:i].strip());start=i+1
    out.append(s[start:].strip());return out
def args(s,start):
    depth=1;i=start
    while depth:
        if s[i]=='(':depth+=1
        if s[i]==')':depth-=1
        i+=1
    return parts(s[start:i-1])
symbol=r'[@%](?:"[^"]+"|[-\w.$]+)'
header=re.compile(r'^define .*?('+symbol+r')\(')
call=re.compile(r'\b(?:call|invoke)\b.*? ('+symbol+r')\(')
x=json.loads((F/'elf-crosscheck.json').read_text());rawrows=json.loads((P/'elf-raw-input.json').read_text())
output=[];pins=[]
for mode,build in [('default','build-default-v3'),('devnet','build-devnet-v1'),('pool','build-pool-v1')]:
    fs=[];calls=[];byraw=collections.defaultdict(list)
    for p in sorted((P/build/'compiler-output').glob('*.ll')):
        pins.append(dict(mode=mode,path=str(p),sha256=sha(p),bytes=p.stat().st_size))
        lines=p.read_text().splitlines()
        f=None
        for n,l in enumerate(p.read_text().splitlines(),1):
            m=header.search(l)
            if m:
                ps=args(l,m.end());params=[]
                for a in ps:
                    v=re.findall(symbol,a);params.append(v[-1] if v else None)
                f=dict(path=str(p),line=n,raw=m[1][1:].strip('"'),params=params,signature=l,assign={},indirect=[],lines=lines)
                fs.append(f);byraw[f['raw']].append(f)
            elif f and l=='}':f=None
            elif f:
                a=re.match(r'\s*('+symbol+r') = (.*)',l)
                if a:f['assign'][a[1]]=dict(line=n,text=a[2])
                m=call.search(l)
                if m:
                    c=dict(path=str(p),line=n,caller=f['raw'],target=m[1],args=args(l,m.end()),text=l.strip(),f=f)
                    calls.append(c)
                    if m[1].startswith('%'):f['indirect'].append(c)
    incoming=collections.defaultdict(list)
    for c in calls:
        if c['target'].startswith('@'):incoming[c['target'][1:].strip('"')].append(c)
    def origin(f,value,seen):
        key=(f['path'],f['raw'],value)
        if key in seen:return dict(kind='cycle',status='OPEN',value=value)
        seen=seen|{key}
        if value.startswith('@'):return dict(kind='symbol',raw=value[1:].strip('"'),status='OBSERVED_CONSTANT')
        if value in f['params']:
            i=f['params'].index(value);sources=[]
            for c in incoming[f['raw']]:
                if i>=len(c['args']):continue
                actual=c['args'][i];vs=re.findall(symbol,actual)
                if len(vs)==1 and re.search(re.escape(vs[0])+r'$',actual):o=origin(c['f'],vs[0],seen)
                elif re.search(r'\bnull$',actual):o=dict(kind='null',status='OBSERVED_CONSTANT')
                else:o=dict(kind='unsupported_actual',text=actual,status='OPEN')
                sources.append(dict(path=c['path'],line=c['line'],caller=c['caller'],actual=actual,origin=o))
            return dict(kind='formal',parameter=value,index=i,raw=f['raw'],incoming=sources,status='OPEN',
                residual='All final-ELF callers/address-taken entry contexts must be accounted for; forwarding observations alone are not a completeness proof.')
        a=f['assign'].get(value)
        # A narrow, fail-closed aggregate field rule. The callee formal is
        # noalias+readonly; the actual is a private alloca, and its field is
        # written by a constant immediately before the call in the same block.
        if a:
            load=re.fullmatch(r'load ptr, ptr ('+symbol+r'), align 8,.*',a['text'])
            gep=f['assign'].get(load[1]) if load else None
            field=re.fullmatch(r'getelementptr inbounds(?: nuw)? i8, ptr ('+symbol+r'), i64 (\d+)',gep['text']) if gep else None
            if field and field[1] in f['params']:
                idx=f['params'].index(field[1]);offset=int(field[2]);param=args(f['signature'],header.search(f['signature']).end())[idx]
                if 'noalias' in param and 'readonly' in param:
                    sources=[]
                    for c in incoming[f['raw']]:
                        actual=c['args'][idx];vs=re.findall(symbol,actual);cf=c['f'];witness=None
                        if len(vs)==1 and 'noalias' in actual and 'readonly' in actual:
                            base=vs[0];alloc=cf['assign'].get(base)
                            # Immediately adjacent instructions, comments ignored;
                            # labels, branches and all other instructions reject.
                            preceding=[(n+1,t.strip()) for n,t in enumerate(cf['lines'][:c['line']-1]) if t.strip() and not t.lstrip().startswith(';')]
                            if alloc and re.fullmatch(r'alloca \[\d+ x i8\], align 8',alloc['text']) and len(preceding)>=2:
                                sn,store=preceding[-1];gn,gtext=preceding[-2]
                                sm=re.fullmatch(r'store ptr ('+symbol+r'), ptr ('+symbol+r'), align 8',store)
                                gm=re.fullmatch(r'('+symbol+r') = getelementptr inbounds(?: nuw)? i8, ptr '+re.escape(base)+r', i64 '+str(offset),gtext)
                                if sm and gm and sm[2]==gm[1] and sm[1].startswith('@') and all(re.findall(symbol,arg).count(base)==0 for j,arg in enumerate(c['args']) if j!=idx):
                                    witness=dict(alloca=alloc,gep=dict(line=gn,text=gtext),store=dict(line=sn,text=store),call=dict(line=c['line'],text=c['text']),offset=offset,base=base)
                                    o=origin(cf,sm[1],seen)
                                else:o=dict(kind='field_write_not_adjacent_constant',status='OPEN')
                            else:o=dict(kind='field_actual_not_private_adjacent',status='OPEN')
                        else:o=dict(kind='field_actual_attributes',status='OPEN')
                        sources.append(dict(path=c['path'],line=c['line'],caller=c['caller'],actual=actual,origin=o,field_witness=witness))
                    return dict(kind='formal',parameter=field[1],index=idx,raw=f['raw'],incoming=sources,status='OPEN',field_load=a,field_gep=gep,field_offset=offset,rule='adjacent constant write into private noalias readonly aggregate')
        return dict(kind='ssa' if a else 'unbound',value=value,definition=a,status='OPEN',
            residual='Typed load/phi/select/aggregate provenance and caller state required; no pointer target invented.')
    for site in x['artifacts'][mode]['indirect_sites']:
        candidates=[]
        symbols=[r for r in rawrows if r['artifact']==mode and int(r['id'].split(':')[2],16)==site['caller']]
        raw={v for r in symbols for v in r['raw_symbol_aliases']}
        for r in raw:
            for f in byraw[r]:
                for c in f['indirect']:
                    candidates.append(dict(raw=r,path=f['path'],definition_line=f['line'],llvm_line=c['line'],text=c['text'],operand_origin=origin(f,c['target'],set())))
        output.append(dict(mode=mode,address=site['address'],caller=site['caller'],caller_symbols=site['caller_symbols'],
            llvm_candidates=candidates,status='OPEN',
            correspondence='Function-level raw-symbol equality only; multiple LLVM indirect calls cannot be paired to an ELF callx by textual order.',
            category='owned_callback' if any(s.startswith(('aspis_','_ZN')) for s in site['caller_symbols']) else 'library_vtable_or_formatting'))
result=dict(schema='s10-pass4-indirect-provenance-v1',inputs=pins,sites=output,
    counts=dict(sites=len(output),with_llvm_candidates=sum(bool(s['llvm_candidates']) for s in output),
        owned_callback_sites=sum(s['category']=='owned_callback' for s in output)),
    generator='tools/s10-inventory5-20261021/indirect-host.py',
    limitation='This retains concrete SSA/formal sources and all observed direct-call arguments. It is not a total pointer analysis or a certificate excluding unseen callbacks.')
p=H/'indirect.json';raw=(json.dumps(result,indent=2,sort_keys=True)+'\n').encode();p.write_bytes(raw)
print(json.dumps(dict(path=str(p),sha256=sha(p),bytes=len(raw),counts=result['counts'])),flush=True)
