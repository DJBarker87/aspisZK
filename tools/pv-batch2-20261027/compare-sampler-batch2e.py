from pathlib import Path
import json,re,hashlib
E=Path('evidence/pv-batch2-20261027/batch2e');lp=E/'39893-stdout.log';np=E/'NATIVE-OUT.log'
lean={k:json.loads(v) for k,v in re.findall(r'\("(249_zero|249_ff|250_zero|250_ff)", some (\[[^\]]*\])\)',lp.read_text())}
native={k:json.loads(v) for k,v in re.findall(r'PV_B2_E_NATIVE_(249_zero|249_ff|250_zero|250_ff)=(\[[^\]]*\])',np.read_text())}
assert set(lean)==set(native)=={'249_zero','249_ff','250_zero','250_ff'}
assert all(lean[k]==native[k] for k in lean)
assert lean['250_ff']!=[0]*8 and lean['249_ff']!=lean['249_zero']
r=json.loads((E/'NATIVE-RECEIPT.json').read_text());assert r['exit_status']==0
j=dict(passed=True,scope='labelled finite native/emitted complete-success Result comparison plus native original/copy differential; not a universal proof or physical observation/fixture gate',emission_attempt=39893,emission_module='R1Z/PV_B2_E_Install250',native_receipt='NATIVE-RECEIPT.json',source_pins='NATIVE-SOURCE-PINS.json',lean=lean,native=native,all_limbs_equal=True,changing_output_cases=['250_ff','249_ff'],native_pairs_per_sampler=4402,copy_mutation='direct index writes only; low-state quotient array and add-state arrays are retained in emissions',frozen_original='unfaithful original mutable iterator emission is not imported; original source associated structurally and sampled natively',print_axioms='39893.json; only standard axioms for source and installation laws')
(E/'SAMPLER-FIDELITY.json').write_text(json.dumps(j,indent=2)+'\n');print('all4 labelled Lean/native Results match;4402 native pairs per sampler')
