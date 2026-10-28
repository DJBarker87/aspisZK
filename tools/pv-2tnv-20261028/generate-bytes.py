from pathlib import Path
import re,hashlib,json,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-2tnv-20261028/resume'
def load(m):
 s=(E/(m+'.lean.txt')).read_text();b=[];names=[]
 for line in s.splitlines():
  if re.match(r'def c\d+',line):
   name=line.split()[1];names.append(name)
   if 'replicate' in line:
    n,v=map(int,re.search(r'replicate (\d+) (\d+)#u8',line).groups());b.extend([v]*n)
   else:b.extend(map(int,re.findall(r'(\d+)#u8',line)))
 return bytes(b),names
p,pnames=load('JFx_DataPublic00');q,qnames=load('JHb_DataRequest');assert q[104:]==p[1664:]
vec=lambda xs:'['+','.join(f'{i}#u8' for i in xs)+']'
s='''import JFx_DataPublic00
import JHb_DataRequest
set_option autoImplicit false
namespace AspisR1.PV_2TNV_ByteEncoding
open Aeneas Aeneas.Std
/-- Little-endian interpretation used only for literal byte field facts here. -/
def littleEndian : List U8 → Nat
  | [] => 0
  | b :: bs => b.val + 256 * littleEndian bs
'''
rules='List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil'
fields=[('snapshot_index',296,8),('snapshot_sequence',288,8),('after_index',984,8),('checkpoint_sequence',104,8),('payment_sequence',1736,8),('asset',1808,4)]
# Correct field offsets follow the fixed 1880-byte source format.
# Digest 00: historical anchor; 01: snapshot current root; 02..21 frontier;
# 22: after root; 23..42 after frontier; 43..46 payment digests.
for k in range(47):
 off=112 if k==0 else 304 if k==1 else 336+32*(k-2) if k<=21 else 992 if k==22 else 1024+32*(k-23) if k<=42 else [1744,1776,1816,1848][k-43]
 fields.append((f'digest_{k:02}',off,32))
# Payment layout is 216 bytes, with 8-byte prefix, pool32/domain32/sequence8,
# anchor32/nullifier32/asset4/recipient32/change32.
fields=[(n,(1808 if n=='asset' else o),l) for n,o,l in fields]
rows=[]
for n,off,size in fields:
 raw=p[off:off+size];assert len(raw)==size
 name=n+'_bytes'
 s+=f'def {name} : List U8 := {vec(raw)}\n'
 s+=f'theorem {n}_selected : (JFx_DataPublic00.bytes.drop {off}).take {size} = {name} := by\n'
 s+='  simp only [JFx_DataPublic00.bytes,'+','.join('JFx_DataPublic00.'+c+'_length' for c in pnames)+','+rules+']\n  rfl\n'
 s+=f'#print axioms {n}_selected\n'
 if size==8 or n=='asset':
  value=int.from_bytes(raw,'little');s+=f'theorem {n}_value : littleEndian ((JFx_DataPublic00.bytes.drop {off}).take {size}) = {value} := by\n  rw [{n}_selected]\n  rfl\n#print axioms {n}_value\n'
 rows.append(dict(name=n,offset=off,size=size,little_endian=int.from_bytes(raw,'little') if size<=8 else None))
s+='''/-- The actual TX2 payment payload and TX1 payment payload agree byte for byte. -/
theorem payment_same : JHb_DataRequest.bytes.drop 104 = JFx_DataPublic00.bytes.drop 1664 := by
'''
s+='  simp only [JHb_DataRequest.bytes,JFx_DataPublic00.bytes,'+','.join('JFx_DataPublic00.'+c+'_length' for c in pnames)+','+','.join('JHb_DataRequest.'+c+'_length' for c in qnames)+','+rules+']\n  rfl\n#print axioms payment_same\nend AspisR1.PV_2TNV_ByteEncoding\n'
target=R/'lean/PV_2TNV_ByteEncoding.lean'
if '--check' in sys.argv:assert target.read_text()==s
else:target.write_text(s)
(E/'byte-generation.json').write_text(json.dumps(dict(public_sha256=hashlib.sha256(p).hexdigest(),request_sha256=hashlib.sha256(q).hexdigest(),source_sha256=hashlib.sha256(s.encode()).hexdigest(),fields=rows,payment_equal=True),indent=2)+'\n')
print('generated literal field facts',len(rows))
