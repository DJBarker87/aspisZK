"""Additive read-only audit. No native scanner certificate is issued here."""
from pathlib import Path
import sys,json,hashlib,lzma,re,copy
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent
sys.path.insert(0,str(E.parent/'slice-s-compose10-20261104'))
import NFD_validate as inherited
sha=lambda b:hashlib.sha256(b).hexdigest()
WRAPPER=['62 0a fc ff 00 00 00 00','bf a4 00 00 00 00 00 00','07 04 00 00 fc ff ff ff','85 10 00 00 ff ff ff ff','61 a0 fc ff 00 00 00 00','67 00 00 00 20 00 00 00','c7 00 00 00 20 00 00 00','95 00 00 00 00 00 00 00']
def instructions(dis):
 out={}
 for line in dis.splitlines():
  m=re.match(r'^\s*([0-9a-f]+): ((?:[0-9a-f]{2} ){7}[0-9a-f]{2})(?:\s|$)',line)
  if m:out[int(m[1],16)]=m[2]
 return out

def wrapper_check(dis,rel):
 code=instructions(dis)
 assert [code[0x1749d0+8*i] for i in range(8)]==WRAPPER
 assert re.search(r'^00000000001749e8 R_SBF_64_32\s+sol_memcmp_\s*$',rel,re.M)
 # Encoded scalar register identities: r1,r2,r3 untouched; result slot r10-4,
 # passed as r4 and loaded into r0, then sign extension only. No body semantic
 # claim follows from this structural audit of the eight instruction bytes.
 return dict(left_register='r1',right_register='r2',length_register='r3',output_slot='r10-4',return_observation='low32(reply)==0',runtime_body_visible=False)

def callsite_check(dis):
 code=instructions(dis)
 expected={
  0x4ab40:'bf a1 00 00 00 00 00 00',0x4ab48:'07 01 00 00 98 fa ff ff',
  0x4ab50:'bf 72 00 00 00 00 00 00',0x4ab58:'b7 03 00 00 b0 02 00 00',
  0x4ab60:'85 10 00 00 cd 53 02 00',0x4ab68:'67 00 00 00 20 00 00 00',
  0x4ab70:'77 00 00 00 20 00 00 00',0x4ab78:'55 00 08 00 00 00 00 00',
  0x4ab80:'71 71 b8 02 00 00 00 00',0x4ab88:'55 01 06 00 02 00 00 00',
  0x50e28:'bf a2 00 00 00 00 00 00',0x50e30:'07 02 00 00 80 fa ff ff',
  0x50e38:'79 a1 70 fa 00 00 00 00',0x50e40:'b7 03 00 00 b0 02 00 00',
  0x50e48:'85 10 00 00 70 47 02 00',0x50e50:'67 00 00 00 20 00 00 00',
  0x50e58:'77 00 00 00 20 00 00 00',0x50e60:'55 00 2a 00 00 00 00 00'}
 assert all(code[a]==b for a,b in expected.items())
 assert 0x4ab68+0x253cd*8==0x1749d0
 assert 0x50e50+0x24770*8==0x1749d0
 return dict(sites=['0x4ab60','0x50e48'],size=688,source_association='ordered length/encode/equality/tag continuation; stripped ELF has no scanner debug name')

def artifacts():
 out={}
 for flavor in ['default','devnet']:
  p=E/('NFH_'+flavor+'_disassembly.txt')
  raw=lzma.decompress(Path(str(p)+'.xz').read_bytes())
  assert sha(raw)==Path(str(p)+'.sha256').read_text().strip()
  dis=raw.decode();rel=(E/('NFH_'+flavor+'_relocations.txt')).read_text()
  out[flavor]=dict(wrapper=wrapper_check(dis,rel),calls=callsite_check(dis))
 return out

def packet_check(packet):
 assert packet['inherits']=='evidence/slice-s-compose10-20261104/NFD_LEDGER_DELTA.json'
 assert packet['new_closed_rows']==packet['new_closed_edges']==packet['new_closed_roots']==0
 assert packet['NFH_certificates']=={}
 assert packet['new_trust_adopted']==[]
 assert packet['scanner_status']=='OPEN'
 assert packet['native_equality_bridge_discharged'] is False
 return True

def compose(base,packet):
 packet_check(packet)
 return copy.deepcopy(base)

def main():
 artifacts_report=artifacts()
 base=inherited.compose(inherited.baseline(),inherited.read(inherited.E/'NFD_LEDGER_DELTA.json'))
 out=compose(base,json.loads((E/'NFH_LEDGER_DELTA.json').read_text()))
 report=inherited.inherited.inherited.inherited.summary(out)
 assert report['closed_row_count']==96 and report['root_closed_count']==6
 edges=json.loads((E/'NFH_EDGES.json').read_text())
 assert edges==json.loads((inherited.E/'NFD_EDGES.json').read_text())
 assert sum(x['status']=='CLOSED' for x in edges)==126
 result=dict(inherited_validation=report,comparison_inspection=artifacts_report,closed_rows=96,closed_edges=126,closed_roots=6,new_closed_rows=0,scanner='OPEN',trust_added=[],target='not yet established')
 (E/'NFH_VALIDATION.json').write_text(json.dumps(result,indent=1)+'\n')
 print(json.dumps({k:v for k,v in result.items() if k not in ['inherited_validation','comparison_inspection']},indent=1))
if __name__=='__main__':main()
