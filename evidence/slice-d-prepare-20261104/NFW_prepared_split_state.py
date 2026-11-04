from pathlib import Path
import json
E=Path(__file__).resolve().parent;p=E/'NFW_prepared_native_prepare.py';s=p.read_text()
s=s.replace('let i:usize=kani::any();kani::assume(i<if o.q_error{5}else{6});\n  let seed_ok=', 'let i=if cfg!(NFW_call0){0}else if cfg!(NFW_call1){1}else if cfg!(NFW_call2){2}else if cfg!(NFW_call3){3}else if cfg!(NFW_call4){4}else{5};kani::assume(i<if o.q_error{5}else{6});\n  let seed_ok=')
s=s.replace('o.lens[i]==[928,32,224,256,2048,0][i])','o.lens[i]==[928,32,224,256,2048,0][i]&&(if i<4{o.nonzero[i]==(i==0)}else{true}))')
s=s.replace('_=>p.rho==o.rho};','14=>p.rho==o.rho,_=>p.variant==Variant::S2};').replace('for j in range(15):','for j in range(16):')
p.write_text(s)
p=E/'NFW_run.py';s=p.read_text();needle="if os.environ.get('NFW_PART') is not None:\n  part=int(os.environ['NFW_PART']);assert 0<=part<5;env['RUSTFLAGS']+=' --cfg NFW_part'+str(part)";s=s.replace(needle,needle+"\n if os.environ.get('NFW_CALL') is not None:\n  call=int(os.environ['NFW_CALL']);assert 0<=call<6;env['RUSTFLAGS']+=' --cfg NFW_call'+str(call)");p.write_text(s)
(E/'NFW_K033_REVIEW.json').write_text(json.dumps(dict(attempt='NFW_K033',disposition='TIMEOUT; zero credit',wall_seconds=94.65672954102047,peak_rss_kib=1511376,swaps=0,replacement='Original prepared_facet3 harness, per-concrete source call index0..5; each on arbitrary input/state/prestate and with matched control. Source-dependent path/active-prefix bounds unchanged, caps unchanged.'),indent=1)+'\n')
