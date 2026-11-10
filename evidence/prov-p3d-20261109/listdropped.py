import re,sys
for m in sys.argv[1:]:
    s=open(f'../prov-p2g-20261109/PRVEq_{m}.lean').read()
    for b in re.finditer(r'/- PRV-FRESH-DROPPED[^\n]*\n(.*?)\n-/\n',s,flags=re.S):
        t=b.group(1)
        d=re.search(r'\ndef\s+(\S+)|^def\s+(\S+)',t)
        nm=(d.group(1) or d.group(2)) if d else ('?'+t[:60])
        flags=[k for k in ['QM31.ZERO','QM31.ONE','M31.ONE','M31.ZERO','CM31.ZERO','from_fn','array_from'] if k in t]
        print(m,nm.strip(),flags)
