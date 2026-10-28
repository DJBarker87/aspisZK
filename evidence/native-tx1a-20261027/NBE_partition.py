"""Isolate the three disjoint row branches after excluded K012 timeout."""
from pathlib import Path
import sys,json,difflib
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import NBE_host as h
R=E.parents[1];base='crates/aspis-r1-cost-probe/src/'
r=h.remote_py(f'from pathlib import Path\nimport json\nb=Path({(h.B+"/NBE_src")!r});print(json.dumps({{n:(b/n).read_text() for n in [{(base+"NBE_multiproof.rs")!r},{(base+"NBE_keys.rs")!r},{(base+"multiproof.rs")!r},{(base+"candidate.rs")!r}]}}))');assert r.returncode==0,r.stderr
files=json.loads(r.stdout);s=files[base+'NBE_multiproof.rs'];assert 'fn NBE_row_case' not in s
start=s.index('#[kani::proof] #[kani::unwind(18)]\nfn NBE_row_state');end=s.index('\n#[kani::proof]',start+1)
new=s[start:end].replace('#[kani::proof] #[kani::unwind(18)]\nfn NBE_row_state()','fn NBE_row_case(which:u8)')
new=new.replace(' let answer:[u8;32]=kani::any();let calls=Cell::new(0);',' kani::assume(if which==0{paired}else if which==1{!paired && length-at>=32}else{!paired && length-at<32});\n let answer:[u8;32]=kani::any();let calls=Cell::new(0);')
s+=new+'''\n#[kani::proof] #[kani::unwind(18)] fn NBE_row_paired(){NBE_row_case(0)}
#[kani::proof] #[kani::unwind(18)] fn NBE_row_supplied(){NBE_row_case(1)}
#[kani::proof] #[kani::unwind(18)] fn NBE_row_short(){NBE_row_case(2)}
''';files[base+'NBE_multiproof.rs']=s
(E/'NBE_harness_v3.patch').write_bytes((E/'NBE_harness.patch').read_bytes());patch=''
for name,new in files.items():
 old=(R/name).read_text() if (R/name).exists() else ''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+name if old else '/dev/null',tofile='b/'+name))
(E/'NBE_harness.patch').write_text(patch)
r=h.remote_py(f'from pathlib import Path\np=Path({(h.B+"/NBE_src/"+base+"NBE_multiproof.rs")!r});p.write_text({s!r})');assert r.returncode==0,r.stderr
for num,name in [(15,'NBE_row_paired'),(16,'NBE_row_supplied'),(17,'NBE_row_short')]:
 x=json.loads((E/'NBE_K012.json').read_text());a=f'NBE_K{num:03}';x['attempt']=a;x['command'][2]=a;x['command'][3]='multiproof::NBE_multiproof::'+name;x['deps_fingerprint']['graph_receipt']=a+'-graph.json';(E/(a+'.json')).write_text(json.dumps(x,indent=2)+'\n')
(E/'NBE_K012_SPLIT.json').write_text(json.dumps(dict(excluded='K012: all-branch row state timeout',replacement=['K015 paired','K016 supplied32','K017 short sibling'],partition='paired OR (not paired AND remaining>=32) OR (not paired AND remaining<32); exhaustive disjoint domains, no caller restriction'),indent=2)+'\n')
r=h.remote_py(f'from pathlib import Path\nimport json\np=Path({(h.B+"/NBE_tmp")!r});removed=[]\nfor f in p.iterdir():\n if f.is_file() and (f.name.startswith("external-sat") or f.name.startswith("smt2_dec_problem")):removed.append(f.name);f.unlink()\nprint(json.dumps(dict(removed=removed,remaining=[f.name for f in p.iterdir()])))');assert r.returncode==0
(E/'NBE_K012_TMP_CLEANUP.json').write_text(r.stdout)
