"""Construct default replay account images; never alter the retained triple.
Pure Python wire-format reproduction, not native execution evidence.
--check validates generated source exactly. PDA diagnostics are not Lean proofs.
"""
from pathlib import Path
import hashlib,json,re,sys
R=Path(__file__).resolve().parents[2]; P=Path(__file__).resolve().parent
pub=bytearray()
for line in (R/'lean/JFx_DataPublic00.lean').read_text().splitlines():
 if re.match(r'def c\d+ :',line):
  t=line.split(':=',1)[1]
  if 'List.replicate' in t:
   n,v=map(int,re.search(r'List.replicate (\d+) (\d+)#u8',t).groups());pub.extend([v]*n)
  else:pub.extend(map(int,re.findall(r'(\d+)#u8',t)))
assert len(pub)==1880 and hashlib.sha256(pub).hexdigest()=='f6bcd49446f1077d2c5ed4be940e91f0be444efc5ae83024ec0700b8c205c331'
b58='123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'
def un58(s):
 n=0
 for c in s:n=n*58+b58.index(c)
 return n.to_bytes(32,'big')
q=2**255-19;d=-121665*pow(121666,q-2,q)%q
# Solana rejects every compressed Edwards point, not only prime subgroup points.
def oncurve(b):
 y=int.from_bytes(b,'little')&((1<<255)-1)
 if y>=q:return False
 y2=y*y%q;v=(d*y2+1)%q
 if not v:return False
 x2=(y2-1)*pow(v,q-2,q)%q
 return x2==0 or pow(x2,(q-1)//2,q)==1
def pda(seeds,program):
 for bump in range(255,-1,-1):
  h=hashlib.sha256(b''.join(seeds)+bytes([bump])+program+b'ProgramDerivedAddress').digest()
  if not oncurve(h):return h,bump
 raise ValueError('no PDA')
pool=bytes([65])*32;regprog=bytes([68])*32;mint=bytes([66])*32
verifier=bytes([95,12,126,84,84,184,191,44,127,237,85,250,26,65,11,162,234,180,193,149,162,190,100,247,226,253,59,0,225,151,154,141])
master,mb=pda([b'aspis-pair-forest-master-v1',mint],pool)
forest,fb=pda([b'aspis-pair-forest-checkpoint-v1',master,(42).to_bytes(8,'little')],pool)
lane,lb=pda([b'aspis-pair-forest-lane-v1',master,b'\x03'],pool)
assert master==pub[8:40] and forest==pub[40:72] and lane==pub[72:104]
profile=bytes.fromhex('57947313d232641ad8157d66bfaffab11e4c3a99331d18f44bfacab6899737d3')
release=bytes.fromhex('e294afbc14ef6afe76b847def44452f84cc3728064657607b544a539ca9b323a')
registry,rb=pda([b'aspis-verifier-registry-v2',master],regprog)
entry,eb=pda([b'aspis-verifier-entry-v2',master,profile,release],regprog)
loader=un58('BPFLoaderUpgradeab1e11111111111111111111111')
rpd,rpb=pda([regprog],loader);vpd,vpb=pda([verifier],loader)
binding=b'ASPISFOREST8'+bytes([2,2,2,8,1,20,1])+bytes(13)
assert len(binding)==32
m=bytearray(384);m[:8]=b'ASM8'+bytes([2,8,1,mb]);m[8:40]=binding;m[40:48]=(43).to_bytes(8,'little');m[48:50]=bytes([255,1])
m[64:69]=b'ASPI\x01';m[72:104]=master;m[104:136]=mint;m[136:168]=un58('TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA');m[168:172]=(77).to_bytes(4,'little');m[176:208]=pub[256:288]
m[208:214]=b'ASPP\x01\x03';m[216:248]=regprog;m[280:312]=bytes([7])*32
f=bytearray(192);f[:8]=b'ASC8'+bytes([2,8,1,fb]);f[8:40]=master;f[40:72]=pub[256:288];f[72:80]=(42).to_bytes(8,'little');f[80:112]=pub[112:144]
l=bytearray(768);l[:8]=b'ASL8'+bytes([2,3,8,20]);l[8:40]=binding;l[40:72]=master;l[72]=lb
l[80:88]=b'ASPT'+bytes([1,20,3,1]);l[88:96]=(13).to_bytes(8,'little');l[96:128]=pub[304:336];l[128:768]=pub[336:976]
r=bytearray(256);r[:8]=b'ASR2'+bytes([3,2,1,rb]);r[8:40]=master;r[72:104]=bytes([7])*32;r[104:112]=(1).to_bytes(8,'little');r[112:120]=(1).to_bytes(8,'little');r[120:152]=regprog;r[152:184]=loader;r[184:216]=rpd;r[216:248]=bytes([165])*32;r[248]=rpb
e=bytearray(320);e[:8]=b'ASE2'+bytes([3,1,1,1]);e[8:40]=master;e[40:72]=verifier;e[72:104]=profile;e[104:136]=release;e[136:168]=loader;e[168:200]=vpd;e[200:232]=bytes([90])*32;e[272:280]=(2**64-1).to_bytes(8,'little');e[280:312]=bytes([7])*32;e[312:314]=bytes([eb,vpb])
request=b'ASQ8'+bytes([1,1,1,0])+profile+release+pool+pub[1664:1880]
assert len(request)==320
images={'Master':m,'Forest':f,'Lane':l,'Registry':r,'Entry':e,'Header':pub[976:1664],'Request':request}
manifest={}
for name,data in images.items():
 mod=('JHg_Data' if name in ('Master','Forest') else 'JHb_Data')+name
 out=['import Aeneas','set_option autoImplicit false',f'namespace AspisR1.{mod}','open Aeneas Aeneas.Std']
 for i in range((len(data)+31)//32):
  chunk=data[32*i:32*(i+1)];term='['+','.join(f'{b}#u8' for b in chunk)+']'
  if len(set(chunk))==1:term=f'List.replicate {len(chunk)} {chunk[0]}#u8'
  out += [f'def c{i:02} : List U8 := {term}',f'theorem c{i:02}_length : c{i:02}.length={len(chunk)} := by simp only [c{i:02},List.length_cons,List.length_nil,List.length_replicate]',f'#print axioms c{i:02}_length']
 ns=(len(data)+31)//32
 out += ['def bytes : List U8 := '+' ++ '.join(f'c{i:02}' for i in range(ns)),f'theorem length : bytes.length={len(data)} := by', '  simp only [bytes,List.length_append,'+','.join(f'c{i:02}_length' for i in range(ns))+']','#print axioms length',f'def value : Slice U8 := ⟨bytes,by rw [length];scalar_tac⟩',f'end AspisR1.{mod}']
 path=R/'lean'/(mod+'.lean');s='\n'.join(out)+'\n'
 if '--check' in sys.argv:assert path.read_text()==s,path
 elif name in ('Master','Forest'):path.write_text(s)
 else:assert path.read_text()==s,path
 manifest[name]=dict(bytes=len(data),sha256=hashlib.sha256(data).hexdigest(),construction='Default native replay images formula; derived retained public fields, fixed documented fixture metadata')
manifest['PDA_diagnostic']=dict(master_bump=mb,forest_bump=fb,lane_bump=lb,registry_bump=rb,entry_bump=eb,registry_key=list(registry),entry_key=list(entry))
s=json.dumps(manifest,indent=2)+'\n'
if '--check' in sys.argv:assert (P/'JHg_DATA.json').read_text()==s
else:(P/'JHg_DATA.json').write_text(s)
print('checked' if '--check' in sys.argv else 'generated',len(images),'small images; retained public unchanged')
