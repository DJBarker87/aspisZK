from KMZ_driver import *
a='KMZ_K070'
if not (E/a/'receipt.json').exists():
 rc=json.loads((E/'KMZ_K032/receipt.json').read_text());sha=rc['source_hashes']['KMZ_windows.rs'];src=(E/'sources'/(sha+'.rs')).read_text()
 needle='raw[j][l] ^ 0u32';assert src.count(needle)==1
 src=src.replace(needle,'raw[j][l] ^ (if j==63 && l==3 {1u32}else{0u32})')
 cfg=json.loads((E/'KMZ_K032.json').read_text());cfg.update(command=['python3','KMZ_gate.py',a,'KMZ_typed_inside_gate'],negative_control=True,parent_gate='KMZ_K032',split='typed_last_limb_control',counterexample_witness={'raw':'all zero','j':63,'l':3,'actual_word':0,'wrong_expected_word':1},note='Additional boundary control: identical typed64 positive domain/configuration, with only the expected value of the final element/final limb deliberately wrong. Does not rerun a timed-out gate.')
 result=run(a,cfg,src)
 print('boundary control',result)
