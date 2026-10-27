from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
D='fast_pairing::canonical::LPg_dot::'
rows=[D+'LPg_qadd_contract','verifier::LPg_verifier::LPg_echeck0','verifier::LPg_verifier::LPg_echeck1','compact::LPg_compact::LPg_check_step','r1_wire::LPg_r1_wire::LPg_validate_step','compact::LPg_compact::LPg_expand_low','compact::LPg_compact::LPg_expand_high']
rows += ['r1_wire::LPg_r1_wire::LPg_decode'+str(p)+'_'+str(c) for p in [0] for c in [0,1]]
rows += ['r1_wire::LPg_r1_wire::LPg_fixed'+str(off) for off in [15,28,73,86]]
rows += ['r1_wire::LPg_r1_wire::LPg_decode_'+s for s in ['invalid_row','offset_overflow','range_error']]
rows += ['verifier::candidate::LPg_candidate::LPg_view'+str(i) for i in range(4)]
rows += [D+'LPg_qsub_contract',D+'LPg_qhalf_contract',D+'LPg_product_contract',D+'LPg_finish_canonical',D+'LPg_dot_witness']
assert len(rows)==25
for i,target in enumerate(rows,6):
 a=f'LPg_K{i:03}'
 if (E/a/'receipt.json').exists():continue
 subprocess.run(['python3',str(E/'LPg_attempt.py'),a,'kani',target],check=True)
 r=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
 if r['exit_status'] and ('error[E' in log or 'could not compile' in log):raise SystemExit('STOP compile failure '+a)
 if r['exit_status'] in [124,137] or 'timed out' in log:
  # No automatic retry; continue only to a different isolated stage.
  raise SystemExit(a+' STOP timed-out shape; split further before next run')
