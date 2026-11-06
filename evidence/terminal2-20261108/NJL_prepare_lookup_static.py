from pathlib import Path
import re,json,subprocess,hashlib,difflib
E=Path(__file__).resolve().parent;src=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal_constants.rs']).decode();ep=[tuple(map(int,m))for m in re.findall(r'CompiledPoolV1PairForestEndpoint\s*\{\s*row:\s*(\d+),\s*slot:\s*(\d+),\s*pattern:\s*(\d+)\s*\}',src)];assert len(ep)==272
keys=json.loads((E/'NJL_LOOKUP_TABLE.json').read_text());g={tuple(k):i for i,k in enumerate(keys['group_keys'])};p={tuple(k):i for i,k in enumerate(keys['pattern_keys'])};tables={}
for consumer in [False,True]:
 prefix='consumer'if consumer else'producer';ends=ep[int(consumer)::2];rows=[];gs=[];ps=[]
 for row,slot,pat in ends:
  group=(2 if consumer else 0)+slot;local=row&15;rows.append(row);gs.append(g[(group,local)]);ps.append(p[(group,pat,local)])
 tables[prefix]=dict(row=rows,gc=gs,pc=ps)
(E/'NJL_LOOKUP_STATIC.json').write_text(json.dumps(dict(source_sha256=hashlib.sha256(src.encode()).hexdigest(),tables=tables,reason='Direct literal expected arrays remove any new Rust reference-loop interpretation from the cut; no extraction needed'),indent=1))
rust=''
for side,data in tables.items():
 for field,values in data.items():rust+=f'const NJL_{side.upper()}_{field.upper()}:[usize;136]=['+','.join(map(str,values))+'];\n'
p=E/'NJL_control.rs.txt';old=p.read_text();new=old+rust
needle='assert_eq!(pc,NJL_pattern_model(group,usize::from(e.pattern),local));'
new=new.replace(needle,needle+'''\n let expected_gc=if consumer{NJL_CONSUMER_GC[index]}else{NJL_PRODUCER_GC[index]};
 let expected_pc=if consumer{NJL_CONSUMER_PC[index]}else{NJL_PRODUCER_PC[index]};
 assert_eq!(gc,expected_gc+if cfg!(NJL_invert){1}else{0});assert_eq!(pc,expected_pc);
''');assert needle in old;p.write_text(new);n='crates/aspis-statement/src/pool_v1/NJL_control.rs';(E/'NJL_LOOKUP_STATIC.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n)));pins=json.loads((E/'NJL_SOURCE_PINS.json').read_text());pins[n]=hashlib.sha256(new.encode()).hexdigest();(E/'NJL_SOURCE_PINS.json').write_text(json.dumps(pins));p=E/'NJL_gate.py';s=p.read_text();key="frozen='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'";s=s.replace(key,"""p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'const NJL_CONSUMER_GC' not in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_LOOKUP_STATIC.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_LOOKUP_STATIC.patch')],cwd=S,check=True)
"""+key);p.write_text(s)
for k,base in [(19,17),(20,18)]:
 x=json.loads((E/f'NJL_K{base:03}.json').read_text());a=f'NJL_K{k:03}';x.update(attempt=a,module='NJL_endpoint_lookup_cut',command=['python3','NJL_gate.py',a+'.json'],expected_time='Strengthened same-name genuine lookup: direct136-cell literal expected arrays, eliminating unextracted reference-loop semantics from cut authority')
 x['native_command']=[v.replace('NJL_pattern_control_cut','NJL_endpoint_lookup_cut')for v in x['native_command']];x['sources']+=['NJL_LOOKUP_STATIC.patch','NJL_LOOKUP_STATIC.json'];x['collect']=[v.replace(f'NJL_K{base:03}',a)for v in x['collect']];(E/(a+'.json')).write_text(json.dumps(x))
# Generated Lean literal arrays share EXACT decimal payloads with Rust. Keep scan for support only.
p=E/'NJL_generate_lookup_lean.py';s=p.read_text();needle="s+='''def scanFrom";insert="""static=json.loads((E/'NJL_LOOKUP_STATIC.json').read_text())['tables']
for side,data in static.items():
 for field,values in data.items():
  s+=f'def {side}_{field} : Fin 136 → Nat := !['+','.join(map(str,values))+']\\n'
""";s=s.replace(needle,insert+needle)
s=s.replace('scanFrom (group index consumer,column index consumer) groupKeys 0','if consumer then consumer_gc index else producer_gc index').replace('scanFrom (group index consumer,(endpoint index consumer).pattern.val,column index consumer) patternKeys 0','if consumer then consumer_pc index else producer_pc index')
p.write_text(s)
print('Strengthened expected values to direct literal arrays; first gate remains the old snapshot, second gate must cover this dependency change')
