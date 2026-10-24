#!/usr/bin/env python3
"""Hash official Cargo sources; retain pointers/line numbers, not GPL source."""
import hashlib,json,pathlib,resource,subprocess,sys,time,urllib.request
T=pathlib.Path(__file__).resolve().parent;E=T.parents[1]/'evidence/sbf-cache-prep-20261024';start=time.monotonic();rows=[]
revs=['ca74c32f0ac6d99000858dcae9b0931ef76a8f43','29ea6fb6a']
files=['src/cargo/util/rustc.rs','src/cargo/core/compiler/fingerprint/mod.rs','src/cargo/core/compiler/custom_build.rs','src/cargo/core/compiler/build_runner/mod.rs']
terms=['workspace_wrapper','rustc_fingerprint','wrapper','build_script','cmd.exec','exec_with','unit_id','RUSTC_WRAPPER']
for rev in revs:
    for name in files:
        url=f'https://raw.githubusercontent.com/rust-lang/cargo/{rev}/{name}';t=time.monotonic()
        with urllib.request.urlopen(url,timeout=20) as r:
            b=r.read(2*1024**2+1);status=r.status
        assert len(b)<=2*1024**2 and status==200
        lines=b.decode().splitlines();matches={s:[i+1 for i,l in enumerate(lines) if s in l] for s in terms}
        rows.append(dict(url=url,revision=rev,path=name,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),status=status,wall_seconds=time.monotonic()-t,lines=matches))
        # Read pertinent bodies in terminal for review; not stored as source.
        if rev==revs[0]:
            for i,l in enumerate(lines):
                if any(s in l for s in ['workspace_wrapper.hash','pub fn fingerprint','fn rustc_fingerprint','cmd.exec','exec_with','RUSTC_WRAPPER']):
                    print(name,i+1,'\n'.join(lines[max(0,i-3):i+6]))
u=resource.getrusage(0)
r=dict(sources=rows,assessment='SBF Cargo exact version ca74c32f0 from new pinned version query; outer host Cargo 29ea6fb6a version reused from merged metadata. Source review is not compiler correctness or loaded compiler closure.',receipt=dict(command=[sys.executable,'-B',str(pathlib.Path(__file__).resolve())],exit=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss,swaps=u.ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),script_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),print_axioms='N/A'))
(E/'cargo-source-research.json').write_text(json.dumps(r,indent=2)+'\n')
