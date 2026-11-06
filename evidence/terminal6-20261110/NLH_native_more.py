from pathlib import Path
import subprocess,sys,json
p=Path(__file__).resolve().parent;base=json.loads((p/'NLH_K024.json').read_text());start=int(sys.argv[1]);lo=int(sys.argv[2]);hi=int(sys.argv[3])
shapes=[('NLH_composition_native','NLH_composition_poseidon_cut'),('NLH_composition_native','NLH_composition_semantic_cut'),('NLH_composition_native','NLH_composition_copy_cut'),('NLH_composition_native','NLH_composition_gather_cut'),('NLH_leaves_native','NLH_composition_selectors_cut'),('NLH_leaves_native','NLH_composition_poseidon_selectors_cut'),('NLH_leaves_native','NLH_composition_prepared_cut'),('NLH_leaves_native','NLH_composition_selected_columns_cut'),('NLH_leaves_native','NLH_composition_variant_cut'),('NLH_parts_native','NLH_terminal_composition_cut')]
for module,harness in shapes[lo:hi]:
 for control in [False,True]:
  a=f'NLH_K{start:03}';start+=1;x=json.loads(json.dumps(base));x['attempt']=a;x['module']=harness;x.pop('deps_fingerprint',None);x['command'][-1]=a+'.json';x['native_command'][x['native_command'].index('--harness')+1]='pool_v1::pair_forest_semantic_terminal::'+module+'::'+harness
  x['env']['RUSTFLAGS']=base['env']['RUSTFLAGS']+(' --cfg NKR_invert'if control else '');x['collect']=[n.replace('NLH_K024',a)for n in x['collect']];x['sources']=[n for n in x['sources']if not n.endswith('.xz')]+['NLH_composition.patch','NLH_Composition_native.rs.txt','NLH_COMPOSITION_TRANSCRIPTION.json','NLH_extend.patch','NLH_Leaves_native.rs.txt','NLH_Parts_native.rs.txt','NLH_EXTEND_TRANSCRIPTION.json'];x['expected_time']='Optimized compilation then '+('matched corrupt-argument/reply control (expected failure) 'if control else 'missing native parent occurrence ')+harness
  (p/(a+'.json')).write_text(json.dumps(x));r=subprocess.run([sys.executable,str(p/'NLH_run.py'),a]);q=p/a/'receipt.json'
  if not q.exists():raise SystemExit('Unresolved receipt; recover read-only, never resubmit')
  s=(p/a/'stdout.log').read_text();ok=(r.returncode==1 and 'VERIFICATION:- FAILED'in s)if control else(r.returncode==0 and 'VERIFICATION:- SUCCESSFUL'in s)
  print(json.dumps(dict(attempt=a,harness=harness,control=control,expected_verdict=ok)),flush=True)
  if not ok:raise SystemExit(1)
