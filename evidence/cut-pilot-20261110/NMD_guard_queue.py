from NMD_native import *
a=int(sys.argv[1])
for shape in ['shared','exclusive']:
 (E/'NMD_native.rs').write_text((E/('NMD_guard_'+shape+'.rs')).read_text())
 for name in ['NMD_guard_real','NMD_guard_cut','NMD_guard_bad_value','NMD_guard_bad_token','NMD_copy_control']:
  attempt=f'NMD_K{a:03}';a+=1;r=native(attempt,'verifier::candidate::NMD_native::'+name)
  log=lzma.decompress((E/attempt/'stdout.log.xz').read_bytes()).decode();assert 'Traceback' not in log and 'Failed to match' not in log and 'could not compile' not in log and 'timed out' not in log.lower(),'Stop unexpected compile error/retire timed-out shape'
  with (E/'NMD_GUARD_RESULTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=attempt,shape=shape,control=name,exit_status=r['exit_status'],timeout='timed out' in log.lower(),domain='free RefCell<u8>, arbitrary payload; minimal callee only, no allocator/ambient effects'))+'\n')
