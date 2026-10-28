from pathlib import Path
import sys,importlib.util
E=Path(__file__).resolve().parent
sys.argv=['upload','none'];s=importlib.util.spec_from_file_location('nbx',E/'NBX_native.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
m.admit('NBX_UPLOAD')
p=E/'NBX_slots.rs.txt';data=p.read_text()
r=m.py(f'from pathlib import Path; Path({(m.B+"/NBU_src/crates/aspis-statement/src/pool_v1/NBX_slots.rs")!r}).write_text({data!r})')
assert r.returncode==0,r.stdout+r.stderr
