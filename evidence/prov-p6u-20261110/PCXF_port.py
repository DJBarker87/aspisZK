"""PCXF_port.py: ports the PCXE_ tools to PCXF_ by one simultaneous textual substitution (rename map in PCXF_TOOLS.json)."""
import re, sys, os, shutil
sys.dont_write_bytecode = True
SRC = 'prov-p6t-20261110'; DST = 'prov-p6u-20261110'
MAP = [('PCXE_', 'PCXF_'), ('PCXD_', 'PCXE_'), ('prov-p6t-20261110', 'prov-p6u-20261110'), ('prov-p6r-20261110', 'prov-p6t-20261110'), ('pc-prov-p6t-20261110', 'pc-prov-p6u-20261110'), ('pc-prov-p6r-20261110', 'pc-prov-p6t-20261110'), ('pc-prov-p6t', 'pc-prov-p6u'), ('PCXE_HOST_BASE', 'PCXF_HOST_BASE')]
rx = re.compile('|'.join(re.escape(a) for a, b in MAP)); d = dict(MAP)
n = 0
for f in sorted(os.listdir(SRC)):
    if not re.fullmatch(r'(PCXE_[A-Za-z0-9_]+\.(sh|py)|PCXE_audit_def\.lean\.in|run_scope\.sh|PRVH_WrapAdd\.lean)', f): continue
    t = open(f'{SRC}/{f}').read()
    t2 = rx.sub(lambda m: d[m[0]], t)
    out = f.replace('PCXE_', 'PCXF_')
    open(f'{DST}/{out}', 'w').write(t2); n += 1
    if f.endswith('.sh'): os.chmod(f'{DST}/{out}', 0o755)
print('ported', n)
