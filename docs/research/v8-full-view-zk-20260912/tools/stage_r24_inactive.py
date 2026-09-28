#!/usr/bin/env python3
"""Source-generated complement/duplicate sharing for unchanged inactive masks."""
import argparse,ast,hashlib,json,re,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();src=a.control;dst=a.output
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((src/'r18-stage.json').read_text());assert 'r24_qm' in m
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';table=ex/'r17_basis_tables.rs'
arrays={x[1]:ast.literal_eval(x[2].replace('true','True').replace('false','False'))for x in re.finditer(r'pub const (\w+):[^=]+=(\s*\[[^;]+\]);',table.read_text())}
order=arrays['ORDER'];inactive=arrays['INACTIVE'];assert len(order)==len(inactive)==1024
masks=[sum(1<<g for g in range(64)if order[16*g+low]!=1023 and inactive[order[16*g+low]])for low in range(16)]
unique=list(dict.fromkeys(masks));ids=[unique.index(x)for x in masks]
assert len(unique)==10 and sum(x.bit_count()for x in masks)==809
rows=[];ends=[0];complements=[]
for mask in unique:
    complement=mask.bit_count()>32;complements.append(complement)
    rows.extend(g for g in range(64)if bool(mask>>g&1)!=complement);ends.append(len(rows))
assert len(rows)==87
fn='''
#[inline(never)]
fn r24_inactive_values(hb:&[K],values:&mut[K;19]) {
'''
fn+=f'    const MASKS:[u64;16]={masks!r};\n    const IDS:[usize;16]={ids!r};\n    const ENDS:[usize;11]={ends!r};\n    const ROWS:[usize;87]={rows!r};\n'
fn+='    const COMPLEMENT:[bool;10]=['+','.join(str(x).lower()for x in complements)+'];\n'
fn+='''    #[cfg(not(target_os="solana"))] {
        let t=basis_transport::transport();
        for low in 0..16 {let mut mask=0u64;for g in 0..64 {let row=t.order[16*g+low];if row!=1023 && t.inactive[row]{mask|=1u64<<g;}}assert_eq!(mask,MASKS[low]);}
    }
    let total=hb[..64].iter().copied().fold(K::ZERO,|s,x|s.add(x));
    let mut shared=[K::ZERO;10];
    for i in 0..10 {
        let mut sum=K::ZERO;
        for j in ENDS[i]..ENDS[i+1] {sum=sum.add(hb[ROWS[j]]);}
        shared[i]=if COMPLEMENT[i]{total.sub(sum)}else{sum};
    }
    for low in 0..16 {values[low]=shared[IDS[low]];}
    let total_b=hb[64..128].iter().copied().fold(K::ZERO,|s,x|s.add(x));
    for low in 0..3 {
        let i=IDS[low];let mut sum=K::ZERO;
        for j in ENDS[i]..ENDS[i+1] {sum=sum.add(hb[64+ROWS[j]]);}
        values[16+low]=if COMPLEMENT[i]{total_b.sub(sum)}else{sum};
    }
}
'''
path=ex/'r22_scalar.rs';text=path.read_text()
start=text.index('    let t=basis_transport::transport();let mut inactive=[K::ZERO;19];')
end=text.index('    let inactive=scalar_low(normal,carry,&inactive);',start)
text=text[:start]+'    let mut inactive=[K::ZERO;19];r24_inactive_values(hb,&mut inactive);\n'+text[end:]+fn
path.write_text(text);m['files'][str(path.relative_to(dst))]=sha(path)
m['r24_inactive']={'source_table_sha256':sha(table),'normal_masks':16,'unique_masks':10,'normal_mask_ones':809,'selected_rows':87,'control_manifest_sha256':sha(src/'r18-stage.json')}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({'stage':str(dst),'mask_screen':m['r24_inactive']}))
