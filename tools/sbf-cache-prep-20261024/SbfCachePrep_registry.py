#!/usr/bin/env python3
"""Exact consumed public Cargo source-package join; never executes Cargo."""
import hashlib,json,os,pathlib,posixpath,re,resource,stat,sys,tarfile,time,tomllib
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));start=time.monotonic();P=pathlib.Path
STAGE=P('/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024');OUT=STAGE/'SbfCachePrep-20261024';BASE=P('/home/dombarker/project-offloads/codex-cx-s10-repin3-20261023');REG=P('/home/dombarker/.cargo/registry')
def digest(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        while b:=f.read(1024**2):h.update(b)
    return h.hexdigest()
def no_links(p):
    for q in (p,*p.parents):assert not q.is_symlink(),str(q)
def possible_key(name):
    return re.search(r'(keypair|private.?key|mnemonic|credential|secret|\.pem$|\.key$|\.env(?:\.|$)|id_rsa)',name,re.I) and P(name).suffix not in ('.rs','.toml','.md','.txt')
no_links(OUT);assert os.getuid()==1000 and stat.S_IMODE(STAGE.stat().st_mode)==0o700
raw=OUT/'inventory.json';assert digest(raw)=='e98de11bf81d5497652882f2663c6eedec3a0aa13a3ae14877f79da946b07541'
assert digest(STAGE/'src/Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
lock=tomllib.loads((STAGE/'src/Cargo.lock').read_text());packages={(p['name'],p['version']):p for p in lock['package']}
consumed={};old_roots=set();info=[]
for r in json.loads(raw.read_text()):
    if r['type']!='regular':continue
    p=BASE/r['path']
    if p.suffix=='.d' and r['bytes']<2*1024**2:
        no_links(p);assert digest(p)==r.get('sha256');text=p.read_text(errors='replace')
        for index,crate,rel in re.findall(r'/home/dombarker/\.cargo/registry/src/([^/\s:]+)/([^/\s:]+)/([^\s:]+)',text):consumed.setdefault((index,crate),set()).add(posixpath.normpath(rel))
        for path in re.findall(r'/home/dombarker/project-offloads/[^\s:]+',text):old_roots.add('/'.join(path.split('/')[:6]))
    elif p.name=='.rustc_info.json':
        no_links(p);assert digest(p)==r['sha256'];x=json.loads(p.read_text())
        # Do not dump cached outputs/environment. Pin compiler version answers.
        answers=[]
        for value in x.get('outputs',{}).values():
            if isinstance(value,dict):value=[value.get('stdout')]
            if isinstance(value,list):
                for s in value:
                    if isinstance(s,str) and s.startswith('rustc ') and 'host:' in s:answers.append(s)
        info.append(dict(path=r['path'],sha256=r['sha256'],rustc_fingerprint=x.get('rustc_fingerprint'),version_answers=answers))
results=[]
for (index,crate),used in sorted(consumed.items()):
    if crate not in {'borsh-1.5.7','five8-0.2.1','five8_const-0.1.4','five8_core-0.1.2','serde_core-1.0.228','syn-1.0.109','version_check-0.9.5','winnow-0.7.15'}:continue
    row=dict(index=index,crate=crate,consumed_paths=len(used));results.append(row)
    try:
        name,version=crate.rsplit('-',1);pkg=packages[(name,version)];assert pkg['source']=='registry+https://github.com/rust-lang/crates.io-index'
        archive=REG/'cache'/index/(crate+'.crate');src=REG/'src'/index/crate;no_links(archive);no_links(src)
        actual=digest(archive);row.update(archive_sha256=actual,archive_bytes=archive.stat().st_size,lock_checksum=pkg['checksum']);assert actual==pkg['checksum']
        expected=set();manifest=[]
        with tarfile.open(archive,'r:gz') as tar:
            members=tar.getmembers();assert len(members)<20000
            # Preflight ALL names/types before reading any source member.
            for m in members:
                rel=pathlib.PurePosixPath(m.name);assert rel.parts[0]==crate and not rel.is_absolute() and '..' not in rel.parts
                assert m.isfile() or m.isdir(),'nonregular source archive member'
                assert not possible_key(rel.name),'possible key/secret filename excluded before member read'
            for m in members:
                if not m.isfile():continue
                rel=str(pathlib.PurePosixPath(m.name).relative_to(crate));expected.add(rel);p=src/rel;no_links(p);s=p.lstat();assert stat.S_ISREG(s.st_mode) and s.st_size==m.size
                f=tar.extractfile(m);h=hashlib.sha256()
                while b:=f.read(1024**2):h.update(b)
                a=h.hexdigest();assert digest(p)==a,'unpacked byte mismatch: '+rel
                manifest.append(dict(path=rel,bytes=m.size,sha256=a))
        row['consumed_missing']=sorted(used-expected);assert used<=expected,'consumed path absent from source archive'
        actual=set()
        for root,ds,fs in os.walk(src,followlinks=False):
            for n in ds+fs:no_links(P(root)/n)
            actual.update(str((P(root)/n).relative_to(src)) for n in fs)
        row['unpacked_extra_names']=sorted(actual-expected);assert actual-expected<={'.cargo-ok','.cargo-checksum.json'},'unexpected unpacked sources'
        row.update(verified=True,files=len(manifest),manifest_sha256=hashlib.sha256(json.dumps(manifest,sort_keys=True).encode()).hexdigest(),source_bytes=sum(m['bytes'] for m in manifest),extra_metadata=sorted(actual-expected))
    except (OSError,ValueError,KeyError,AssertionError,tarfile.TarError) as e:row.update(verified=False,error=str(e)[:256],error_type=type(e).__name__)
output=OUT/'registry-focused-join.json'
with output.open('x') as f:json.dump(dict(packages=results,old_roots=sorted(old_roots),rustc_info=info),f,sort_keys=True);f.write('\n')
u=resource.getrusage(0)
print(json.dumps(dict(packages=len(results),verified=sum(r.get('verified',False) for r in results),failures=[r for r in results if not r.get('verified')],old_roots=sorted(old_roots),rustc_info=info,output=dict(path=str(output),bytes=output.stat().st_size,sha256=digest(output)),receipt=dict(command=[sys.executable,'-'],exit=0,wall_seconds=time.monotonic()-start,peak_rss_kib=u.ru_maxrss,swaps=u.ru_nswap,print_axioms='N/A'),limitations='Current sequential public registry comparison; no package execution, complete build-script input closure or TOU claim'),sort_keys=True))
