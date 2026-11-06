from pathlib import Path
import subprocess,json,hashlib,os
B=Path.cwd();rows=[]
for name,path in [('cargo-kani','/home/dombarker/.cargo/bin/cargo-kani'),('kani-rustc','/home/dombarker/.kani/kani-0.67.0/toolchain/bin/rustc'),('sbf-rustc','/home/dombarker/.rustup/toolchains/1.89.0-sbpf-solana-v1.52/bin/rustc'),('lean',os.environ['LEAN_SYSROOT']+'/bin/lean')]:
 p=Path(path);r=subprocess.run([str(p),'--version'],capture_output=True,text=True);assert r.returncode==0,(name,r.stderr)
 rows.append(dict(name=name,path=str(p),resolved=str(p.resolve()),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),version=r.stdout.strip(),exit=r.returncode))
assert '0.67.0' in rows[0]['version'];assert '1.93.0' in rows[1]['version'];assert '1.89.0' in rows[2]['version'];assert '4.32.0' in rows[3]['version']
(B/'NLF_TOOL_PINS.json').write_text(json.dumps(dict(tools=rows,CARGO_TARGET_DIR=os.environ['CARGO_TARGET_DIR'],note='Final tool identity inspection; exact per-attempt commands/environment remain in raw receipts. No verification run or extraction launched here.'),indent=1)+'\n')
print('NLF tool pins match cargo-kani 0.67.0, Kani rustc 1.93, SBF rustc 1.89 and Lean 4.32')
