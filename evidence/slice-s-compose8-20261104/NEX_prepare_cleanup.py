"""Separate all-error Box frame check; no successful child domain is assumed."""
from NEX_native_patch import E
import sys,subprocess,json,re
family,mode=sys.argv[1:];assert family in ['afterstate','snapshot'];assert mode in ['positive','negative']
subprocess.run([sys.executable,str(E/'NEX_prepare_decoder.py'),family,'positive'],check=True)
m=json.loads((E/'NEX_DECODER_CURRENT.json').read_text());s=m['source'];variant='Afterstate' if family=='afterstate' else 'Snapshot';value='c.lane_transition.'+('candidate_afterstate' if family=='afterstate' else 'live_snapshot');err='PoolV1PairVerifierTransportErrorV1' if family=='afterstate' else 'PoolV1PairLiveSnapshotErrorV1'
s=s.replace(f'let reply=if kani::any(){{Ok({value})}}else{{Err(NEE_any_{err}())}};',f'let reply=Err(NEE_any_{err}());')
s=s.replace(f'(Err(PoolV1PairLatePublicStatementErrorV1::{variant}(e)),Err(expected))=>assert!(e==expected)',f'(Err(PoolV1PairLatePublicStatementErrorV1::{variant}(e)),Err(expected))=>{{assert!(e==expected);assert!(f.allocated.is_null());}}')
if mode=='negative':s=s.replace('f.calls=1;f.reply','f.calls=1;f.allocated=Box::into_raw(Box::new(NEE_common().lane_transition.'+('candidate_afterstate' if family=='afterstate' else 'live_snapshot')+'));f.reply')
p=E/'NEX_native_contracts.patch';patch=p.read_text();start=patch.index('@@ -0,0 ');patch=patch[:start]+'@@ -0,0 +1,'+str(len(s.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in s.splitlines());p.write_text(patch)
m.update(mode='error_'+mode,source=s,classification='aa clause iii, arbitrary full error reply, no native Box allocation; negative oracle makes an unauthorized allocation without changing error result')
(E/'NEX_CLEANUP_CURRENT.json').write_text(json.dumps(m,indent=1))
