from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;n='crates/aspis-r1-cost-probe/src/r1_semantic.rs';p=E/'NIX_src'/n;s=p.read_text();a=s.index('  assert_eq!(l.decode_row,row);');b=s.index('  match out{',a);c=s.index('\n }\n}',b)
left=s[a:b];left=left.replace('  let boundary_ok=same(bd,running);let has_semantic=decode_ok&&boundary_ok;let has_value=has_semantic&&semantic_ok;','')
common='  let boundary_ok=same(bd,running);let has_semantic=decode_ok&&boundary_ok;let has_value=has_semantic&&semantic_ok;\n'
s=s[:a]+common+'  #[cfg(NIX_round_args)] {if negative {l.ptr=core::ptr::null();l.frame^=1;}\n'+left+'  }\n  #[cfg(NIX_round_result)] {\n'+s[b:c]+'\n  }'+s[c:];p.write_text(s)
pins=json.loads((E/'NIX_SOURCE_PINS.json').read_text());pins[n]=hashlib.sha256(p.read_bytes()).hexdigest();(E/'NIX_SOURCE_PINS.json').write_text(json.dumps(pins));(E/'NIX_round_split.rs.txt').write_text(s[s.index('#[cfg(kani)] pub mod NIX_round'):])
x=json.loads((E/'NIX_L066.json').read_text());x.update(attempt='NIX_L070',module='Split timed-out round133 argument/frame and return observations',sources=['NIX_src/'+n,'NIX_SOURCE_PINS.json'],command=['python3','-c','print("K060 combined observation retired; independent args/frame and result partitions only")']);x['collect']=[];(E/'NIX_L070.json').write_text(json.dumps(x,indent=2))
(E/'NIX_K061_UNSUBMITTED.json').write_text((E/'NIX_K061.json').read_text())
for i,kind,negative in [(61,'args',False),(68,'args',True),(69,'result',False),(70,'result',True)]:
 a=f'NIX_K{i:03}';x=json.loads((E/'NIX_K060.json').read_text());x.update(attempt=a,module='NIX_round_program::'+('control' if negative else 'native'));x['command'][2]=a+'.json';x['native_command'][x['native_command'].index('--harness')+1]=x['module'];x['env']['RUSTFLAGS']='-Copt-level=3 -C link-arg=-Wl,--threads=1 --cfg NIX_round_'+kind;x['collect']=[a+s for s in ['-graph-check.json','-graph.stderr','-graph.json','-source-check.json','-lock-check.json']];x['expected_time']='Optimized single round '+kind+' observation; K060 combined shape retired';(E/(a+'.json')).write_text(json.dumps(x,indent=2))
