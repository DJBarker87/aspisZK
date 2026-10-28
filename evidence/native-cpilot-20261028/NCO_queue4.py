from pathlib import Path
import subprocess,sys,os,json
E=Path(__file__).resolve().parent
rows=[
('r1_wire::NCO_wire::shape_contract',None),('r1_wire::NCO_wire::shape_caller',None),('r1_wire::NCO_wire::shape_caller_wrong',None),('r1_wire::NCO_wire::shape_contract','NCO_invert_shape'),
('compact::NCO_compact::compact_row_contract',None),('compact::NCO_compact::compact_row_caller',None),('compact::NCO_compact::compact_row_wrong',None),('compact::NCO_compact::compact_row_contract','NCO_invert_compact'),
('compact::NCO_compact::copy_positive',None),('compact::NCO_compact::copy_negative',None),
('compact::NCO_compact::expand_contract',None),('compact::NCO_compact::expand_contract','NCO_invert_expand'),
('r1_wire::NCO_wire::validate_contract',None),('r1_wire::NCO_wire::validate_callsite',None),('r1_wire::NCO_wire::validate_contract','NCO_invert_validate'),('r1_wire::NCO_wire::validate_contract','NCO_weak_validate'),('r1_wire::NCO_wire::validate_callsite','NCO_weak_validate'),
('NCO_controls::result_slice_negative',None),('NCO_controls::result_slice_real',None),('NCO_controls::result_slice_frame',None),('NCO_controls::vec_negative',None),('NCO_controls::vec_real',None),('NCO_controls::vec_frame',None)]
assert len(rows)==23
for i,(target,cfg) in enumerate(rows,48):
 env=dict(os.environ)
 if cfg:env['NCO_RUST_CFG']=cfg
 a=f'NCO_K{i:03}'
 r=subprocess.run([sys.executable,str(E/'NCO_run.py'),a,'kani',target],env=env)
 if r.returncode:raise SystemExit(r.returncode)
 log=(E/a/'stdout.log').read_text()
 # Compiler/validation errors in a new family are inspected before continuing.
 if 'could not compile' in log or 'Traceback' in log:raise SystemExit('inspect compiler/input failure '+a)
