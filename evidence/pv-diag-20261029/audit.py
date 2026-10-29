"""Conservative syntactic inventory; NOT a universal reachability certificate.

Read-only reuse of the deployed release corpus. Each shard is a disjoint input
partition, not a repeated regression. Raw guards are retained without pretending
to know that their operands are public. Generic/unlinked bodies remain candidates.
"""
from pathlib import Path
import collections, hashlib, json, lzma, re, subprocess, sys
D = Path('/home/dombarker/project-offloads/codex-pv-diag-20261029')
P = D.parent / 'codex-pv-rdea-20261028'
T = P / 'client-target/release/deps'
S = D.parent / 'codex-pv-fscan-20261028/src'
R = Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu')
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(name, x):
    (D / name).write_text(json.dumps(x, indent=2)+'\n')
def zsave(name, x):
    with lzma.open(D/name, 'wt') as f: json.dump(x, f)
patterns = {
 'stdout': r'\b_print\b|\bprint_to\b|\bstdout\b',
 'stderr': r'\b_eprint\b|\bstderr\b|write_error|panic_output',
 'write_candidate': r'\b(?:write|write_all|write_fmt|write_vectored|pwrite|pwrite64|writev|fwrite|puts|putchar|send|sendto|sendmsg|syscall)\b',
 'log_candidate': r'\b(?:log|tracing|slog|sol_log|logger|Log)::|__private_api.*log',
 'panic': r'\bpanic(?:_|\b)|\b(?:assert_failed|unwrap_failed|expect_failed|begin_panic|rust_panic|rust_begin_unwind)\b',
 'panic_hook': r'\b(?:default_hook|set_hook|take_hook|update_hook|rust_panic_with_hook)\b',
 'backtrace': r'\b(?:Backtrace|backtrace_rs|backtrace)::|\b(?:_Unwind_Backtrace|backtrace|Capture|force_capture)\b',
 'error_format_candidate': r'anyhow::|strerror|from_utf8_lossy|estimated_capacity|addr2line|symbolize',
}
rx = {k:re.compile(v, re.I if k=='backtrace' else 0) for k,v in patterns.items()}
def classes(s): return [k for k,v in rx.items() if v.search(s)]

def scan(index):
    pins=json.loads((P/'ir-mir-pins.json').read_text())
    files=[(k,r) for k in ('mir','llvm') for r in pins[k]]
    for p in sorted((P/'stdlib-ir').glob('*.ll.xz')):
        files.append(('stdlib',dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size)))
    files=files[index::46]
    rows=[]; checks=[]; functions=[]; inline=[]; cfgs=[]
    # Demangled comments in the compiler's own LLVM are preferable to a guessed
    # mangling parser. Cross-unit targets come from the inherited complete map.
    with lzma.open(P/'ir-unit-qualified-graph.json.xz','rt') as f: names=json.load(f)['names']
    def llvm_flush(cur, blocks, found):
        if not found:return
        cfg_id=len(cfgs)
        cfgs.append(dict(function=cur,terminators=blocks))
        for r in found:
            r['local_cfg_id']=cfg_id
            rows.append(r)
    for kind,pin in files:
        p=Path(pin['path']); actual=sha(p)
        assert actual==pin['sha256'],str(p)
        checks.append(dict(**pin,kind=kind,actual_sha256=actual))
        op=lzma.open if p.suffix=='.xz' else open
        with op(p,'rt',errors='replace') as f:
            cur=''; block='entry'; blocks={}; found=[]; comment=''
            for n,line in enumerate(f,1):
                if kind=='mir':
                    if line.startswith('fn '):
                        llvm_flush(cur,blocks,found);cur=line.strip();block='entry';blocks={};found=[]
                        if '-> Result<' in cur or '-> std::result::Result<' in cur:
                            functions.append(dict(file=str(p),line=n,function=cur,kind='Result_return_signature'))
                    m=re.match(r'    (bb\d+)(?: \(cleanup\))?: \{',line)
                    if m:block=m[1]
                    if re.search(r'\b(?:switchInt|assert|goto|resume|return|unreachable)\b| -> \[',line) and not line.lstrip().startswith('//'):
                        blocks.setdefault(block,[]).append(dict(line=n,text=line.strip()))
                    cs=[]
                    if '->' in line and not line.lstrip().startswith('//'):cs=classes(line)
                    if re.search(r'_0 = (?:std::result::)?Result.*::Err\(',line):cs.append('returned_error_candidate')
                    if re.search(r'\bassert\(',line):cs.append('panic')
                    if cs:found.append(dict(kind=kind,file=str(p),line=n,function=cur,block=block,classes=sorted(set(cs)),instruction=line.strip(),classification='UNRESOLVED',trigger='Execution reaches this basic block; see full local terminators. Operand provenance and entry reachability unproved.'))
                    if '(inlined ' in line:
                        cs=classes(line)
                        if cs:inline.append(dict(file=str(p),line=n,function=cur,classes=cs,text=line.strip(),classification='INLINE_SCOPE_CANDIDATE'))
                else:
                    if line.startswith('; ') and not line.startswith('; Function Attrs'):comment=line[2:].strip()
                    if line.startswith('define '):
                        llvm_flush(cur,blocks,found);cur=comment or line.strip();block='entry';blocks={};found=[]
                    m=re.match(r'^([-\w.$]+):',line)
                    if m:block=m[1]
                    if re.match(r'\s*(?:br |switch |indirectbr |ret |resume |unreachable|invoke )',line):
                        blocks.setdefault(block,[]).append(dict(line=n,text=line.strip()))
                    if re.search(r'\b(?:call|invoke)\b',line) and not line.lstrip().startswith(';'):
                        m=re.search(r'@("[^"\n]+"|[-\w.$]+)\(',line)
                        target=m[1].strip('"') if m else ''
                        name=names.get(target,names.get(p.name+'::'+target,target))
                        cs=classes(name)
                        if not m and ' asm ' not in line:cs.append('indirect_call_candidate')
                        if ' asm ' in line:cs.append('inline_assembly_candidate')
                        if cs:found.append(dict(kind=kind,file=str(p),line=n,function=cur,block=block,target=target,target_name=name,classes=cs,instruction=line.strip(),classification='UNRESOLVED',trigger='Execution reaches callsite; raw branch/return terminators retained. Indirect callee/argument provenance unproved.'))
            llvm_flush(cur,blocks,found)
    zsave(f'shard-{index:02}.json.xz',dict(inputs=checks,sites=rows,local_cfgs=cfgs,result_signatures=functions,inlined_scopes=inline,complete_universal_sink_enumeration=False))
    counts=collections.Counter(c for r in rows for c in r['classes'])
    save(f'shard-{index:02}-summary.json',dict(files=len(checks),sites=len(rows),inlined_scopes=len(inline),result_signatures=len(functions),counts=counts))
    print(index,len(checks),len(rows),dict(counts))

def features():
    out=[]
    for p in sorted((P/'client-target/release/.fingerprint').glob('*/*.json')):
        x=json.loads(p.read_text())
        if 'features' in x:out.append(dict(path=str(p),sha256=sha(p),record=x))
    save('resolved-build-units.json',dict(profile='release; opt-level 3, debug assertions off, overflow checks off, panic unwind',requested_features=['r1p-check','aspis-r1-cost-probe/ct-host-prover'],units=out,toolchain=subprocess.check_output([str(R/'bin/rustc'),'-vV'],text=True),lock_sha256=sha(S/'tools/r1-cost-probe/Cargo.lock')))
    checks=[]
    for x in json.loads((D/'source-identity.json').read_text())['checks']:
        checks.append(dict(path=x['path'],expected=x['sha256'],actual=sha(S/x['path'])))
    assert all(x['expected']==x['actual'] for x in checks)
    save('host-source-identity.json',checks)
    print('units',len(out),'source matches',len(checks))

def backtrace():
    A=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/anyhow-1.0.104')
    paths=[A/'src/backtrace.rs',A/'src/error.rs',A/'src/fmt.rs',A/'Cargo.toml',R/'lib/rustlib/src/rust/library/std/src/backtrace.rs',R/'lib/rustlib/src/rust/library/std/src/panicking.rs',R/'lib/rustlib/src/rust/library/std/src/panic.rs',R/'lib/rustlib/src/rust/library/std/src/process.rs']
    for p in paths:
        text=p.read_text(); dest='source-'+('anyhow-' if p.is_relative_to(A) else 'std-')+p.name+'.txt'
        (D/dest).write_text(text)
    save('backtrace-source-pins.json',[dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size) for p in paths])
    mir=next(T.glob('anyhow-*.mir')).read_text()
    snippets=[]
    for i,line in enumerate(mir.splitlines(),1):
        if any(s in line for s in ['Backtrace::capture','request_ref_backtrace','backtrace_if_absent','Backtrace::force_capture']):snippets.append(dict(line=i,text=line))
    save('anyhow-mir-capture-sites.json',snippets)
    print('source files',len(paths),'anyhow MIR capture references',len(snippets))

def machine():
    b=P/'client-deployed-baseline';assert sha(b)=='fa888460b2c37bee087afd6289cd55219fe2732ea1e1c75011147ed15c260348'
    (D/'image-symbols.txt').write_text(subprocess.check_output(['nm','-anC',str(b)],text=True))
    (D/'dynamic-imports.txt').write_text(subprocess.check_output(['nm','-D','--undefined-only',str(b)],text=True))
    raw=subprocess.check_output(['objdump','-dC','--no-show-raw-insn',str(b)],text=True)
    (D/'image-disassembly.sha256').write_text(hashlib.sha256(raw.encode()).hexdigest()+'\n')
    rows=[];cur=''
    for n,line in enumerate(raw.splitlines(),1):
        m=re.match(r'^[0-9a-f]+ <(.*)>:',line)
        if m:cur=m[1]
        if re.search(r'\b(?:call|jmp)\b',line):
            m=re.search(r'<(.*)>',line); name=m[1] if m else ''
            cs=classes(name)
            if '*' in line:cs.append('indirect_machine_transfer')
            if cs:rows.append(dict(line=n,function=cur,classes=cs,instruction=line.strip(),classification='UNRESOLVED'))
        if re.search(r'\bsyscall\b',line):rows.append(dict(line=n,function=cur,classes=['syscall_candidate'],instruction=line.strip(),classification='UNRESOLVED'))
    zsave('image-sites.json.xz',rows)
    save('image.json',dict(path=str(b),sha256=sha(b),bytes=b.stat().st_size,sites=len(rows),counts=collections.Counter(c for r in rows for c in r['classes']),complete_source_mapping=False))
    print('image sites',len(rows))

def aggregate():
    counts=collections.Counter();inputs=[];sites=inline=results=0
    for i in range(46):
        with lzma.open(D/f'shard-{i:02}.json.xz','rt') as f:x=json.load(f)
        inputs+=x['inputs'];sites+=len(x['sites']);inline+=len(x['inlined_scopes']);results+=len(x['result_signatures'])
        for r in x['sites']:counts.update(r['classes'])
    assert len(inputs)==len(set(x['path'] for x in inputs))
    save('summary.json',dict(inputs=len(inputs),sites=sites,inlined_scopes=inline,result_signatures=results,counts=counts,complete_universal_sink_enumeration=False,reason='Syntactic conservative candidate inventory, not full interprocedural effect/value analysis. Local CFG retained. Missing names, fully inlined/lowered writes, opaque dependencies and native correspondence are not proved covered.',lean_attempts=0,kani_attempts=0,native_scopes=50))
    print(dict(counts), 'inputs',len(inputs),'sites',sites)

if __name__=='__main__':
    mode=sys.argv[1]
    print('Expected time: read-only deployed artifact/source analysis; no compilation, proof generation or elimination.',flush=True)
    if mode=='scan':scan(int(sys.argv[2]))
    else:globals()[mode]()
