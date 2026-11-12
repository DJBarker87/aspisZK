import subprocess,hashlib,sys,re
R='/Users/dominic/ZK'
def src(rev,path): return subprocess.check_output(['git','show',f'{rev}:{path}'],cwd=R)
def body_hash(rev,path,name,start):
    b=src(rev,path); lines=b.split(b'\n')
    # locate fn line at or after start
    i=start-1
    assert re.search(rb'\bfn '+name.encode()+rb'\b',lines[i]), (name,start,lines[i][:80])
    off=sum(len(l)+1 for l in lines[:i])
    j=b.index(b'{',off)       # opening brace of body (signature has no braces before it)
    depth=0;k=j
    while True:
        c=b[k:k+1]
        if c==b'{':depth+=1
        elif c==b'}':
            depth-=1
            if depth==0:break
        k+=1
    endline=b[:k].count(b'\n')+1
    return hashlib.sha256(b[j:k+1]).hexdigest(),endline
PIN='c7593d23fdc';FRZ='3d700effcab'
H='programs/aspis-pool/src/history.rs';F='programs/aspis-pool/src/pair_forest.rs'
rows=[('POOL:285',H,'validate_root_page_bytes',119,131,'8090c436bf1f403498b559c87915dad2fa420451d1053e52a08c6867bea1db37'),
('POOL:301',F,'account_is_zeroed_program_page',806,806,'8f5e8738cda62ae44bbb0fd82af42ffed8c515a8c46fbd24ddcf51f5914ad09e'),
('POOL:340',F,'validate_lane_current_page',817,817,'fc48818f923fdf74a26594fb0d94dc41203290677625f768e9b7bb01f45aa8bf'),
('POOL:322',F,'plan_pair_forest_spend_layout_v1',1218,1218,'51801b29cf49055552b83fd3e82d970e3682e77e41617cc76778d1d88c220c9b'),
('POOL:330',F,'process_pair_forest_terminal_with_verifier_v1',1615,1615,'49900881a1301d8138c9e1589ca3821f8a0e9d21f2b40d16f4e115905dd826f5'),
('POOL:333',F,'require_program_owned_zeroed',400,400,'b82d2e8616bfd7ef54ebcc5ee0404c29cc9effe0b8b3ef5b6c91589d7b86ddea'),
('(new)',H,'page_bytes_are_zero',None,60,None)]
print('row\tfunction\tpin_ledger_hash_reproduced\tfrozen_lines\tfrozen_body_sha256\tchanged')
for rid,p,n,s0,s1,ledger in rows:
    rep='-'
    if s0:
        h0,e0=body_hash(PIN,p,n,s0); rep='YES' if h0==ledger else f'NO({h0[:8]})'
    h1,e1=body_hash(FRZ,p,n,s1)
    print(f'{rid}\t{n}\t{rep}\t{s1}-{e1}\t{h1}\t{"-" if not s0 else ("yes" if h1!=ledger else "no")}')
