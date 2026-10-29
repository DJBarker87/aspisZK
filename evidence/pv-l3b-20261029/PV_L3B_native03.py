from pathlib import Path
import sys,json,hashlib,subprocess,lzma
D=Path(__file__).resolve().parent
sys.path.insert(0,str(D/'python'))
from elftools.elf.elffile import ELFFile
B=D.parent/'codex-pv-rdea-20261028/client-deployed-baseline'
N=D/'client-target/release/devnet_spend'
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):
    with p.open('rb') as f:
        e=ELFFile(f);s=e.get_section_by_name('.text')
        return s.data(),s['sh_addr'],{s.name:dict(size=s['sh_size'],address=s['sh_addr']) for s in e.iter_sections()}
a,aa,asec=read(B);b,ba,bsec=read(N)
assert sha(B.read_bytes())=='fa888460b2c37bee087afd6289cd55219fe2732ea1e1c75011147ed15c260348'
diff=[];start=None
for i in range(max(len(a),len(b))):
    neq=i>=len(a) or i>=len(b) or a[i]!=b[i]
    if neq and start is None:start=i
    if not neq and start is not None:diff.append([start,i]);start=None
if start is not None:diff.append([start,max(len(a),len(b))])
with lzma.open(D/'text-difference-intervals.json.xz','wt') as f:json.dump(dict(meaning='maximal unequal intervals at equal section offsets; not an instruction alignment',baseline_base=aa,debug_base=ba,intervals=diff),f)
def symbols(p):
    s=subprocess.check_output(['nm','-S','-n','-C',str(p)],text=True)
    (D/(p.name+('-baseline' if p==B else '-debug')+'-symbols.txt')).write_text(s)
    out={}
    for line in s.splitlines():
        parts=line.split(maxsplit=3)
        if len(parts)==4 and parts[2] in ['t','T','w','W']:
            try:out.setdefault(parts[3],[]).append([int(parts[0],16),int(parts[1],16)])
            except ValueError:pass
    return out
sa,sb=symbols(B),symbols(N)
rows=[dict(name=k,baseline=sa[k],debug=sb.get(k),same=sa[k]==sb.get(k)) for k in sa]
(D/'symbol-address-comparison.json').write_text(json.dumps(rows,indent=2)+'\n')
r=dict(baseline_sha256=sha(B.read_bytes()),debug_sha256=sha(N.read_bytes()),baseline_text_sha256=sha(a),debug_text_sha256=sha(b),baseline_text_base=hex(aa),debug_text_base=hex(ba),baseline_text_bytes=len(a),debug_text_bytes=len(b),text_identical=a==b,unequal_bytes=sum(y-x for x,y in diff),unequal_intervals=len(diff),first_difference=diff[0] if diff else None,symbols_baseline=len(sa),symbols_debug=len(sb),same_symbol_addresses=sum(x['same'] for x in rows),debug_sections={k:v for k,v in bsec.items() if k.startswith('.debug')},interpretation='Exact shipped DWARF companion' if a==b and aa==ba and all(x['same'] for x in rows) else 'DWARF is a guide only; no exact shipped inline attribution from this build')
(D/'debug-identity.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
