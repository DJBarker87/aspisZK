from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;s=(E/'NIX_round_split.rs.txt').read_text()
s=s.replace('struct Log{','struct Log{getter_prefix:[u64;2],getter_row:[u8;2],getter_count:usize,')
insert=''' fn get(prefix:u64,row:u8,framed:&[u8],l:&mut Log)->Result<ValidatedRecord<'_>,Error>{unreachable!()}'''
# Explicit lifetime ties the returned validation token to the SAME framed borrow.
insert=""" fn get<'a>(prefix:u64,row:u8,framed:&'a[u8],l:&mut Log)->Result<ValidatedRecord<'a>,Error>{let i=l.getter_count;l.getter_prefix[i]=prefix;l.getter_row[i]=row;l.getter_count+=1;Ok(crate::r1_wire::NIX_round_constructor::record(row,framed))}\n"""
s=s.replace(' fn tick(',insert+' fn tick(')
s=s.replace('prefix:&Prefix<\'_>,mut transcript','prefix:u64,framed:&[u8],mut transcript').replace('prefix.validated_record(row)?','get(prefix,row,framed,log)?')
a=s.index('  let bytes:[[u8;3717];27]');b=s.index('  let round:usize=',a)
s=s[:a]+'''  let bytes:[u8;3717]=kani::any();let len:usize=kani::any();kani::assume(len<=3717);let framed=&bytes[..len];let prefix:u64=kani::any();
'''+s[b:]
s=s.replace('let mut l=Log{','let mut l=Log{getter_prefix:[0;2],getter_row:[0;2],getter_count:0,').replace('step(&prefix,t,','step(prefix,framed,t,').replace('records[row as usize].as_ptr()','framed.as_ptr()').replace('sizes[row as usize]','len')
a=s.index('  #[cfg(NIX_round_args)] {');b=s.index('\n  assert_eq!(l.decode_row',a)
s=s[:b]+'''\n  assert_eq!(l.getter_prefix[0],prefix);assert_eq!(l.getter_row[0],row);assert_eq!(l.getter_count,if has_semantic{2}else{1});if has_semantic{assert_eq!(l.getter_prefix[1],prefix);assert_eq!(l.getter_row[1],row);}else{assert_eq!(l.getter_prefix[1],0);assert_eq!(l.getter_row[1],0);}
'''+s[b:]
(E/'NIX_round_local.rs.txt').write_text(s)
(E/'NIX_install_round_local.py').write_text('''from pathlib import Path
import json,hashlib
B=Path(__file__).resolve().parent;n='crates/aspis-r1-cost-probe/src/r1_semantic.rs';p=B/'NIX_src'/n;s=p.read_text();s=s[:s.index('#[cfg(kani)] pub mod NIX_round')]+(B/'NIX_round_local.rs.txt').read_text();p.write_text(s)
nw='crates/aspis-r1-cost-probe/src/r1_wire.rs';p=B/'NIX_src'/nw;s=p.read_text();mark='#[cfg(kani)] pub mod NIX_round_constructor {';s=s.replace(mark,mark+"\\n pub fn record<'a>(row:u8,framed:&'a[u8])->super::ValidatedRecord<'a>{super::ValidatedRecord{row,framed}}\\n");p.write_text(s)
pins=json.loads((B/'NIX_SOURCE_PINS.json').read_text())
for x in [n,nw]:pins[x]=hashlib.sha256((B/'NIX_src'/x).read_bytes()).hexdigest()
(B/'NIX_SOURCE_PINS.json').write_text(json.dumps(pins));print('Prefix is an opaque borrowed-identity token; pure getter packet NIX_ProducerInstall.lookup supplies same row/frame. No physical-prefix assumption or new runtime trust.')
''')
x=json.loads((E/'NIX_L072.json').read_text());x.update(attempt='NIX_L076',module='Replace round prefix construction with CLOSED getter identity log',sources=['NIX_round_local.rs.txt','NIX_install_round_local.py'],command=['python3','NIX_install_round_local.py'],collect=['NIX_SOURCE_PINS.json']);(E/'NIX_L076.json').write_text(json.dumps(x,indent=2))
for i,kind,negative in [(73,'args',False),(74,'args',True),(75,'result',False),(76,'result',True)]:
 a=f'NIX_K{i:03}';x=json.loads((E/'NIX_K069.json').read_text());x.update(attempt=a,module='NIX_round_program::'+('control' if negative else 'native'));x['command'][2]=a+'.json';x['native_command'][x['native_command'].index('--harness')+1]=x['module'];x['env']['RUSTFLAGS']='-Copt-level=3 -C link-arg=-Wl,--threads=1 --cfg NIX_round_'+kind;x['collect']=[a+z for z in ['-graph-check.json','-graph.stderr','-graph.json','-source-check.json','-lock-check.json']];x['expected_time']='Optimized round '+kind+' cut on CLOSED getter borrowed identity, same arbitrary selected frame; no full Prefix construction';(E/(a+'.json')).write_text(json.dumps(x,indent=2))
