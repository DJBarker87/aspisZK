"""Nine intended association-edge corruptions paired to retained split passes."""
from pathlib import Path
import difflib, hashlib, json, subprocess, sys
E = Path(__file__).resolve().parent
REV = '4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
MODES = ['runtime-context','runtime-order','decode-pointer','decode-length','saved-frame','validator-place','lane-place','encoder-place','decoded-output']

def prepare(mode):
 assert mode in MODES, mode
 positive = 'NFR_K021' if mode == 'decoded-output' else 'NFR_K013'
 path = E / (positive+'-shape.json')
 assert path.exists(), 'Generate only after matched positive shape is retained'
 base = json.loads(path.read_text())
 assert base['mode'] == ('value-3' if mode == 'decoded-output' else 'byte'), base['mode']
 source = base['source']
 def replace(old, new):
  nonlocal source
  assert source.count(old) == 1, (mode, old, source.count(old))
  source = source.replace(old, new)
 if mode == 'runtime-context':
  replace('    runtime.invoke(&instruction, &infos)?;', '    let different = Instruction{program_id:instruction.program_id,accounts:Vec::new(),data:Vec::new()};\n    runtime.invoke(&different, &infos)?;')
  intended = 'Runtime invoke assertion checks SAME Instruction address; replacement has equal fields but a different live place'
 elif mode == 'runtime-order':
  replace('    runtime.clear_return_data();\n    runtime.invoke(&instruction, &infos)?;', '    runtime.invoke(&instruction, &infos)?;\n    runtime.clear_return_data();')
  intended = 'Runtime invoke before clear fails the local calls==1 check; native clear/invoke order is necessary'
 elif mode == 'decode-pointer':
  replace('    let result = decode(&returned_data,frame)', '    let different = [0u8;792];\n    let result = decode(&different,frame)')
  intended = 'Decoder argument has the correct length but points to a different live allocation; exact-window identity check fails'
 elif mode == 'decode-length':
  replace('    let result = decode(&returned_data,frame)', '    let result = decode(&returned_data[..791],frame)')
  intended = 'Decoder argument retains the original base pointer but has length791; length check fails'
 elif mode == 'saved-frame':
  replace('let (returned_program, returned_data) = runtime', 'let (returned_program, mut returned_data) = runtime')
  replace('    Ok(AuthenticatedPairForestResultV1 {', '    returned_data[frame.j] ^= 1;\n    Ok(AuthenticatedPairForestResultV1 {')
  intended = 'Mutate the observed saved byte after decoder input checks; saved Box byte equality fails'
 elif mode == 'validator-place':
  replace(' validate(result,f)?;', ' let different=*result;\n validate(&different,f)?;')
  intended = 'Pass an equal typed value from a distinct stack place to validation; SAME authenticated getter pointer check fails'
 elif mode == 'lane-place':
  replace(' let _next_lane_image=lane(result,f)?;', ' let different=*result;\n let _next_lane_image=lane(&different,f)?;')
  intended = 'Pass an equal typed value from a distinct stack place to lane advancement; SAME pointer check fails on the reached successful validation branch'
 elif mode == 'encoder-place':
  replace(' let result_bytes=terminal_bytes(result,f)?;', ' let different=*result;\n let result_bytes=terminal_bytes(&different,f)?;')
  intended = 'Pass an equal typed value from a distinct stack place to reencoding; SAME pointer check fails on the reached successful validation/lane branch'
 else:
  replace('        value: Box::new(result),', '        value: Box::new({let mut changed=result;changed.output_lane^=1;changed}),')
  intended = 'Corrupt output_lane after decoding before boxing; family3 native reply-to-getter equality fails'
 shape = dict(mode='control-'+mode, source=source, harness=base['harness'], base=path.name,
   base_sha256=hashlib.sha256(path.read_bytes()).hexdigest(), matched_positive=positive,
   classification='Negative control only; changes one association edge in an already passing SAME-object source cut',
   intended_failure=intended, accepted_domain=base['accepted_domain'], negative_control=True,
   credit_scope='Same scoped source-cut observations as matched positive; no enclosing process claim')
 return shape

def patch_for(source):
 patch = ''
 for path in ['programs/aspis-pool/src/pair_forest_dispatch.rs','programs/aspis-pool/src/lib.rs']:
  frozen = subprocess.check_output(['git','show',REV+':'+path],text=True)
  hook = frozen+'\n#[cfg(kani)]\n#[path="NFR_CJoin.rs"]\nmod NFR_CJoin;\n' if path.endswith('pair_forest_dispatch.rs') else '#![cfg_attr(kani, feature(allocator_api))]\n'+frozen+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NFO_KMX;\n'
  patch += ''.join(difflib.unified_diff(frozen.splitlines(True),hook.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
 path='programs/aspis-pool/src/NFR_CJoin.rs'
 return patch+'--- /dev/null\n+++ b/'+path+'\n@@ -0,0 +1,'+str(len(source.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in source.splitlines())

if __name__ == '__main__':
 mode=sys.argv[1]
 if mode == '--check':
  checked=[]
  for name in MODES:
   if name == 'decoded-output' and not (E/'NFR_K021-shape.json').exists():continue
   shape=prepare(name);patch=patch_for(shape['source']);assert patch and shape['harness']=='pair_forest_dispatch::NFR_CJoin::association'
   checked.append(name)
  print(json.dumps(dict(checked=checked,proof_launched=False,files_written=False)))
 else:
  shape=prepare(mode)
  (E/'NFR_C_native.patch').write_text(patch_for(shape['source']))
  (E/'NFR_C_CURRENT.json').write_text(json.dumps(shape,indent=1)+'\n')
