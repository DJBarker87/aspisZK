"""Small symbolic read-domain applications; no generated arithmetic cells."""
from pathlib import Path
import json,sys,hashlib,subprocess,re
E=Path(__file__).resolve().parent
# Frozen literal wire sizes and actual source call intervals. These are
# domain components, not complete native caller certificates.
layouts={
 'Request':(320,[('profile',8,40),('release',40,72),('pool_program',72,104),('payment',104,320)]),
 'Statement':(1880,[('master',8,40),('checkpoint',40,72),('lane',72,104),('sequence',104,112),('anchor',112,144),('late',144,1664),('payment',1664,1880)]),
 'Payment':(216,[('pool',8,40),('deployment',40,72),('sequence',72,80),('anchor',80,112),('nullifier',112,144),('asset',144,148),('amount',148,152),('recipient_destination',152,184),('change',184,216)]),
 'Afterstate':(688,[('index',8,16),('root',16,48)]),
 'Snapshot':(800,[('pool',48,80),('deployment',80,112),('sequence',112,120),('index',120,128),('root',128,160)]),
 'Late':(1520,[('header_width',10,12),('snapshot_width',12,16),('afterstate_width',16,20),('total_width',20,24),('snapshot',32,832),('afterstate',832,1520)]),
 'Result':(792,[('master',8,40),('lane',40,72),('nullifier',72,104),('afterstate',104,792)])}
manifest={}
for group,(size,ranges) in layouts.items():
 lines=['import NED_ReadDomains','set_option autoImplicit false',f'namespace NED_{group}ReadWindows','open Aeneas Aeneas.Std Result']
 for name,start,stop in ranges:
  width=stop-start;assert 0<=start<=stop<=size and width<=1880
  lines += [f'theorem {name} (bytes : Array U8 {size}#usize) :',
   '    (do let s ← core.array.Array.index',
   '          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))',
   f'          bytes {{start:={start}#usize,«end»:={stop}#usize}}',
   f'        core.array.TryFromArrayCopySlice.try_from {width}#usize core.marker.CopyU8 s) =',
   f'    ok (.Ok (NBP_Read.chunk (W:={width}#usize) bytes {start} (by decide))) :=',
   f'  NED_ReadDomains.converted bytes {start}#usize {stop}#usize (by decide) (by decide) (by decide)',
   f'#print axioms {name}']
 lines += [f'end NED_{group}ReadWindows']
 text='\n'.join(lines)+'\n';p=E/f'NED_{group}ReadWindows.lean'
 if '--check' in sys.argv:assert p.read_text()==text,str(p)
 else:p.write_text(text)
 manifest[group]=dict(module=p.stem,size=size,ranges=[list(r) for r in ranges],source_sha256=hashlib.sha256(text.encode()).hexdigest(),proof_method='symbolic NED_ReadDomains.converted; only tiny literal bound checks; no concrete bytes normalized')
p=E/'NED_WINDOW_MANIFEST.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==manifest
else:p.write_text(json.dumps(manifest,indent=1)+'\n')
print('checked' if '--check' in sys.argv else 'generated',sum(len(x['ranges']) for x in manifest.values()),'symbolic window laws')
