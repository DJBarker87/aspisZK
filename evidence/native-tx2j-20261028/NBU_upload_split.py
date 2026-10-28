from pathlib import Path
import importlib.util,sys,json
E=Path(__file__).resolve().parent;sys.argv=['upload','none'];s=importlib.util.spec_from_file_location('native',E/'NBU_native.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
m.admit('NBU_SPLIT_UPLOAD')
texts={n:(E/f'NBU_{n}.rs.txt').read_text() for n in ['decode','more']}
for n,text in texts.items():
 r=m.py(f'from pathlib import Path;Path({(m.B+"/NBU_src/crates/aspis-statement/src/pool_v1/NBU_"+n+".rs")!r}).write_text({text!r})');assert r.returncode==0,r.stdout+r.stderr
