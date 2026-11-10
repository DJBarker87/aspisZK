import sys, hashlib, struct
def sections(p):
    b=open(p,"rb").read()
    shoff=struct.unpack_from("<Q",b,0x28)[0]; shentsize,shnum,shstrndx=struct.unpack_from("<HHH",b,0x3A)
    hdr=[struct.unpack_from("<IIQQQQIIQQ",b,shoff+i*shentsize) for i in range(shnum)]
    so=hdr[shstrndx][4]
    out={}
    for h in hdr:
        name=b[so+h[0]:b.index(b"\0",so+h[0])].decode()
        data=b"" if h[1]==8 else b[h[4]:h[4]+h[5]]
        out[name]=(h[5],hashlib.sha256(data).hexdigest()[:16])
    return out
a=sections(sys.argv[1]); c=sections(sys.argv[2])
for k in sorted(set(a)|set(c)):
    x=a.get(k); y=c.get(k)
    print(("SAME " if x==y else "DIFF ")+k, x, y)
