import subprocess,re,json,sys
F="4bb3b3f51e16b4525f1d10336e2b0bcbbd775387";B="b936275465600469312d1f058cdc91ea2a11f3dc"
def git(*a): return subprocess.run(["git","-C","/Users/dominic/ZK",*a],capture_output=True,text=True).stdout
pat=re.compile(r'try_borrow_mut_data|try_borrow_mut_lamports|\.data\.borrow_mut|\.lamports\.borrow_mut|\.borrow_mut\(|RefCell|UnsafeCell|\bCell<|\bCell::new|\.realloc\(|\.assign\(|set_owner|\*\*[A-Za-z_\[\]\.0-9]*lamports|\.resize\(|invoke_signed\(|program::invoke\(|set_return_data')
kinds=[("try_borrow_mut_data","try_borrow_mut_data"),("try_borrow_mut_lamports","try_borrow_mut_lamports"),("data.borrow_mut","data_borrow_mut"),("lamports.borrow_mut","lamports_borrow_mut"),("realloc","realloc"),(".assign(","assign"),("set_owner","set_owner"),("invoke_signed","cpi_invoke_signed"),("program::invoke(","cpi_invoke"),("set_return_data","set_return_data"),("RefCell","RefCell"),("UnsafeCell","UnsafeCell"),("Cell","Cell"),("borrow_mut","borrow_mut"),("**","lamports_deref_write")]
def kind(l):
    for k,n in kinds:
        if k in l: return n
    return "other"
fnre=re.compile(r'^\s*(?:pub(?:\([a-z]+\))?\s+)?(?:const\s+)?(?:unsafe\s+)?fn\s+([A-Za-z_0-9]+)')
out=[]
def scan(rev,paths,scope):
    files=[f for f in git("ls-tree","-r","--name-only",rev,"--",*paths).split() if f.endswith(".rs")]
    for f in files:
        txt=git("show",f"{rev}:{f}").split("\n")
        fn=None;intest=False;pend=False;depth=0;tdepth=None
        for i,l in enumerate(txt,1):
            st=l.strip()
            if re.match(r'#\[cfg\((all\()?test\b',st) or st.startswith('#[test]'): pend=True
            elif pend and st and not st.startswith('#['):
                if re.search(r'\b(mod|fn)\b',st) and tdepth is None: tdepth=depth
                pend=False
            intest = tdepth is not None
            depth+=l.count('{')-l.count('}')
            endtest = tdepth is not None and depth<=tdepth and ('}' in l or ';' in l) and not pend
            m=fnre.match(l)
            if m: fn=m.group(1)
            s=l.strip()
            if s.startswith("//"):
                if endtest: tdepth=None
                continue
            if pat.search(l):
                tst = intest or "/tests/" in f or f.endswith("tests.rs") or "_tests" in f or "/benches/" in f
                out.append(dict(rev=rev[:7],file=f,line=i,fn=fn,kind=kind(l),test_or_cfgtest=bool(tst),text=s[:160]))
            if endtest: tdepth=None
scan(F,["crates","programs/r1-cost-probe"],"frozen")
scan(B,["programs/aspis-pool","programs/aspis-verifier","programs/aspis-registry"],"pool")
json.dump(out,open(sys.argv[1],"w"),indent=1)
