from KND_driver import *
import KND_runtime as runtime
r=t.recover('KND_K069');log=(E/'KND_K069/stdout.log').read_text()
status='TIMEOUT' if 'timed out' in log.lower() or r['exit_status']==124 else 'PASS' if 'VERIFICATION:- SUCCESSFUL' in log else 'COUNTEREXAMPLE' if 'VERIFICATION:- FAILED' in log else 'ERROR'
assert status not in ['COUNTEREXAMPLE','ERROR'],status
(E/'KND_K069/classification.json').write_text(json.dumps(dict(result=status,control=False,parent='KND_K069',source_sha256=r['source_hashes']['KND_windows.rs']),indent=2)+'\n')
cfg=json.loads((E/'KND_K069.json').read_text());row=cfg['transition']
cfg.update(command=['python3','KND_gate.py','KND_K070','KND_transition'],negative_control=True,parent_gate='KND_K069')
control=run('KND_K070',cfg,runtime.source(row,True))
assert control not in ['PASS','ERROR'],control
p=E/'KND_runtime.py';old=p.read_text();(E/'KND_runtime_finite_index.py').write_text(old)
s=old.replace('let initial:[u8;{n}]','let initial:[u8;{c}]')
fragment=' let mut out=alloc::vec::Vec::with_capacity({c});\n KMX_stubs::KMX_extend_from_slice(&mut out,&initial);'
assert fragment in s
s=s.replace(fragment,' let mut out=alloc::vec::Vec::from(initial);out.truncate({n});')
p.write_text(s)
(E/'KND_CONSTRUCTOR_CHANGE.json').write_text(json.dumps(dict(last_old_pair=['KND_K069','KND_K070'],positive=status,control=control,host_attempt_interrupted=False,ssh_child_completed_before_local_queue_terminated=True,terminal_receipt_recovered_read_only=True,first_changed_attempt='KND_K071',change='Use arbitrary array1768 via Vec::from, then truncate to concrete live length, preserving cap1768. Avoid prefix initialization via thousands of Vec::push operations. Every live index remains asserted. No new stub, same harness name, no submitted shape rerun.',old_generator_sha256=hashlib.sha256(old.encode()).hexdigest(),new_generator_sha256=hashlib.sha256(s.encode()).hexdigest()),indent=2)+'\n')
with (E/'KND_KANI.log').open('a') as f:
 subprocess.run([sys.executable,str(p)],stdout=f,stderr=subprocess.STDOUT,check=True)
