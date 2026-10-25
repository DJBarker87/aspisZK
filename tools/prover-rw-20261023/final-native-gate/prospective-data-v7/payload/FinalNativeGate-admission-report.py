"""Admission report read-only diagnostic SOURCE. Public main disabled pending lead review.
No runtime/receiver admission change. All content is untrusted DiagnosticBytes.
Future stdin payload is these exact bytes plus the sealed explicit footer.
"""
import hashlib
import json
import math
import os
import signal
import stat

CHAIN=('home','dombarker','final-native-gate','FinalNativeGate-setup-packet')
NAMES=('prospective-report.json',)
FILE_LIMIT=2**21
TOTAL_LIMIT=2**21
SELECTED_LIMIT=65536
FIELDS=('decision','collection_failures','phase','error','errors','reason','reasons','schema')


def stamp(s):
    return (s.st_dev,s.st_ino,s.st_mode,s.st_uid,s.st_gid,s.st_nlink,
            s.st_size,s.st_mtime_ns,s.st_ctime_ns)


def metadata(s):
    return dict(zip(('dev','ino','mode','uid','gid','nlink','size','mtime_ns','ctime_ns'),stamp(s)))


def directory(s,index):
    if not stat.S_ISDIR(s.st_mode) or s.st_uid not in (0,os.getuid()) or s.st_mode&0o022:
        raise ValueError('root/current-owner nonwrite literal ancestor required')
    if index>=2 and s.st_uid!=os.getuid():raise ValueError('home/stage/packet currentUID required')
    if index>=3 and stat.S_IMODE(s.st_mode)!=0o700:raise ValueError('stage/packet0700 required')


def unique(pairs):
    result={}
    for key,value in pairs:
        if key in result:raise ValueError('duplicate JSON key')
        result[key]=value
    return result


def finite(value):
    raise ValueError('nonfinite JSON constant')


def finite_float(value):
    number=float(value)
    if not math.isfinite(number):raise ValueError('nonfinite JSON number')
    return number


SEMANTIC_KEYS=('allowed','collection_failures','phase','error','errors','reason','reasons','schema',
               'cap_ok','available_ok','legacy_nonreserve_gate_ok','adopted','type','errno')


def semantic_value(key,value):
    # Concrete policy decision embeds legacy visibility and full observations.
    # Never export those nested raw structures through a selected-field wrapper.
    if key=='decision' and type(value) is dict:
        return {k:semantic_value(k,v) for k,v in value.items() if k in SEMANTIC_KEYS}
    if key=='collection_failures' and type(value) is dict:
        return {k:({n:semantic_value(n,v) for n,v in item.items() if n in ('error','type','errno','reason','reasons')}
                   if type(item) is dict else item)
                for k,item in value.items() if k in ('visibility','before','after')}
    if type(value) is dict:
        excluded=('legacy','original_legacy','process_visibility','service_visibility','docker_visibility',
                  'raw_receipts','raw_inputs','read_attempts','orderedinput','ordered_input','env',
                  'environment','snapshots','before_observation','after_observation')
        return {k:semantic_value(k,v) for k,v in value.items() if k not in excluded}
    if type(value) is list:return [semantic_value(key,v) for v in value]
    return value


def selected_fields(value):
    if type(value) is not dict:raise ValueError('top-level JSON dict required')
    selected={};used=2
    for key in FIELDS:
        if key not in value:continue
        raw=json.dumps(value[key],sort_keys=True,ensure_ascii=True,allow_nan=False,separators=(',',':')).encode('ascii')
        row=dict(size=len(raw),sha256=hashlib.sha256(raw).hexdigest())
        # Budget includes keys, hashes, sizes, punctuation and content together.
        projected=semantic_value(key,value[key])
        row['hash_encoding']='complete original field canonical JSON: sorted keys,ASCII,compact'
        candidate=dict(row,value=projected)
        cost=len(json.dumps({key:candidate},sort_keys=True,ensure_ascii=True,allow_nan=False).encode('ascii'))+1
        # Reserve bounded omission records for all following selected fields.
        if used+cost+len(FIELDS)*512<=SELECTED_LIMIT:
            row['value']=projected
        else:
            row['truncation_error']='selected field exceeds combined64KiB budget; content omitted'
        selected[key]=row
        used=len(json.dumps(selected,sort_keys=True,ensure_ascii=True,allow_nan=False).encode('ascii'))
    if used>SELECTED_LIMIT:raise ValueError('selected combined64KiB bound')
    return selected


def collect():
    # Every opened fd is retained only for this bounded interval, closed even on
    # alarm/error. No /proc, process, environment, glob, cache or command reads.
    held=[];checks=[];seen=set();total=0
    result=dict(kind='DiagnosticBytes',trusted=False,execution_authority=False,
                approval=False,identity_gate=False,GO=False,context_promotion=False,
                print_axioms='N/A',files={},ancestors=[],errors=[],
                current_writer='UNOBSERVED; possible concurrent writers; all content untrusted')
    try:
        fd=os.open('/',os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW|os.O_CLOEXEC);held.append(fd)
        root=os.fstat(fd);directory(root,0);checks.append((fd,root,None,None))
        result['ancestors'].append(dict(path='/',metadata=metadata(root)))
        path=''
        for index,part in enumerate(CHAIN,1):
            before=os.stat(part,dir_fd=fd,follow_symlinks=False);directory(before,index)
            sub=os.open(part,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW|os.O_CLOEXEC,dir_fd=fd);held.append(sub)
            opened=os.fstat(sub)
            if stamp(before)!=stamp(opened):raise ValueError('ancestor entry/fd race')
            if (opened.st_dev,opened.st_ino) in seen:raise ValueError('ancestor alias')
            seen.add((opened.st_dev,opened.st_ino));checks.append((sub,opened,fd,part))
            fd=sub;path+='/'+part;result['ancestors'].append(dict(path=path,metadata=metadata(opened)))
        for name in NAMES:
            row=dict(kind='DiagnosticBytes',trusted=False);result['files'][name]=row
            try:
                before=os.stat(name,dir_fd=fd,follow_symlinks=False);row['metadata']=metadata(before)
                original=(stat.S_ISREG(before.st_mode) and before.st_nlink==1 and before.st_uid==os.getuid() and not before.st_mode&0o022)
                row['original_receiver_predicate']=bool(original)
                # Only the observed file group-write bit gets a separate debug
                # read exception. Ownership/type/link/world-write remain strict.
                if not stat.S_ISREG(before.st_mode) or before.st_nlink!=1 or before.st_uid!=os.getuid() or before.st_mode&0o002:
                    raise ValueError('diagnostic file owner/type/link/worldwrite denial')
                row['group_write_exception']=bool(before.st_mode&0o020)
                if not 0<=before.st_size<=FILE_LIMIT:
                    row['hash_unavailable']='complete hash would exceed2MiB read bound; no bytes read'
                    raise ValueError('report exceeds2MiB; bounds denial; no parse/fetch')
                identity=(before.st_dev,before.st_ino)
                if identity in seen:raise ValueError('file alias')
                seen.add(identity)
                src=os.open(name,os.O_RDONLY|os.O_NOFOLLOW|os.O_NONBLOCK|os.O_CLOEXEC,dir_fd=fd);held.append(src)
                if stamp(os.fstat(src))!=stamp(before):
                    row['drift']=True;raise ValueError('file entry/fd race')
                checks.append((src,before,fd,name))
                h=hashlib.sha256();size=0;pieces=[]
                include=True
                while size<before.st_size:
                    raw=os.read(src,min(65536,before.st_size-size))
                    if not raw:break
                    size+=len(raw);total+=len(raw)
                    if size>FILE_LIMIT or total>TOTAL_LIMIT:raise ValueError('diagnostic byte bound')
                    h.update(raw)
                    if include:pieces.append(raw)
                if size!=before.st_size:
                    row['drift']=True;raise ValueError('file size drift')
                if stamp(os.fstat(src))!=stamp(before) or stamp(os.stat(name,dir_fd=fd,follow_symlinks=False))!=stamp(before):
                    row['drift']=True;raise ValueError('file interval drift')
                row.update(size=size,sha256=h.hexdigest())
                try:
                    value=json.loads(b''.join(pieces).decode('utf-8','strict'),object_pairs_hook=unique,parse_constant=finite,parse_float=finite_float)
                    row['selected_fields']=selected_fields(value)
                except (ValueError,RecursionError,OverflowError) as exc:row['parse_error']=str(exc)[:512]
            except TimeoutError:
                raise
            except (OSError,ValueError) as exc:
                row['error']=str(exc)
        if any(row.get('drift') for row in result['files'].values()):raise ValueError('file race denies whole diagnostic interval')
        for opened,before,parent,name in checks:
            if stamp(os.fstat(opened))!=stamp(before):raise ValueError('final fd drift')
            if parent is not None and stamp(os.stat(name,dir_fd=parent,follow_symlinks=False))!=stamp(before):
                raise ValueError('final entry drift')
        result['interval_stable']=True
    except (OSError,ValueError,TimeoutError) as exc:
        # Deny drift: no content/hash result from a failed whole observation.
        for row in result['files'].values():
            for key in ('selected_fields','sha256','size'):row.pop(key,None)
        result['interval_stable']=False;result['errors'].append(str(exc))
    finally:
        for opened in reversed(held):
            try:os.close(opened)
            except OSError as exc:
                result['errors'].append('fd close: '+str(exc));result['interval_stable']=False
    return result


def diagnostic_entry():
    def alarm(*_):raise TimeoutError('read-only diagnostic10s alarm')
    signal.signal(signal.SIGALRM,alarm);signal.alarm(10)
    try:
        result=collect()
        print(json.dumps(result,sort_keys=True,allow_nan=False))
        return 78 if result['errors'] or any('error' in row or 'parse_error' in row for row in result['files'].values()) else 0
    finally:signal.alarm(0)


def main():
    print('FinalNativeGate admission report SOURCE disabled; lead review/new allocation required')
    return 78


if __name__=='__main__':raise SystemExit(main())
