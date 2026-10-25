#!/usr/bin/python3 -I
"""Exact source-justified metadata rustc query guard; no build-script claim."""
import hashlib,json,os,pathlib,sys
BASE=pathlib.Path('/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024/SbfResolve-20261025-v1')
def queries():
 q=['-','--crate-name','___','--print=file-names']
 tail=[]
 for kind in ['bin','rlib','dylib','cdylib','staticlib','proc-macro']:tail+=['--crate-type',kind]
 tail+=['--print=sysroot','--print=split-debuginfo','--print=crate-name','--print=cfg','-Wwarnings']
 return [ ['-vV'],q+tail,q+['--target','sbpf-solana-solana']+tail ]
def permitted(argv,rustc):return bool(argv and argv[0]==rustc and argv[1:] in queries())
def main():
 c=json.loads((BASE/'control.json').read_text());a=sys.argv[1:]
 allowed=permitted(a,c['rustc'])
 # Exact sequences exclude real file inputs, response files, --emit, -o,
 # --out-dir, -C, -Z and every other unknown option. '-' only for PRINT query.
 if allowed:
  h=hashlib.sha256(pathlib.Path(a[0]).read_bytes()).hexdigest()
  allowed=h==c['rustc_sha256']
 else:h=None
 with (BASE/'compiler-queries.jsonl').open('a') as f:f.write(json.dumps(dict(argv=a,allowed=allowed,binary_sha256=h,pid=os.getpid()))+'\n')
 if not allowed:return 97
 # Cargo source sends empty stdin; never forward source bytes.
 if sys.stdin.buffer.read(1):return 98
 fd=os.open('/dev/null',os.O_RDONLY);os.dup2(fd,0);os.close(fd)
 os.execve(a[0],a,dict(os.environ))
if __name__=='__main__':sys.exit(main())
