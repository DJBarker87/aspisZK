from pathlib import Path
import subprocess,sys,json,lzma
E=Path(__file__).resolve().parent
jobs=[(76,'sdk_summary_all_lengths_drop_wrong',1,'a.try_borrow_mut_data().is_ok()'),(77,'sdk_summary_all_lengths_argument_wrong',1,'src as *const u8'),(78,'snapshot_selected_words',0,'VERIFICATION:- SUCCESSFUL'),(79,'snapshot_selected_words_wrong',1,'Failed Checks:'),(80,'rejected_construct_all_words',0,'VERIFICATION:- SUCCESSFUL'),(81,'rejected_construct_all_words_wrong',1,'Failed Checks:')]
for n,h,expected,check in jobs:
 a=f'NHJ_K{n:03}';assert not (E/a).exists()
 r=subprocess.run([sys.executable,str(E/'NHJ_run.py'),a,'kani','r1_pool_adapter::owned::NHJ_owned::'+h],capture_output=True,text=True);(E/(a+'-controller.log')).write_text(r.stdout+r.stderr)
 f=E/a/'receipt.json'
 if not f.exists():raise RuntimeError('Recover submitted job read-only; no resubmission')
 x=json.loads(f.read_text());s=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode();ok=x['exit_status']==expected and check in s and 'timed out' not in s
 with (E/'NHJ_SNAPSHOT_FINISH.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,expected=expected,exit=x['exit_status'],valid=ok))+'\n')
 print(a,ok,flush=True)
 if not ok:raise RuntimeError('Review before dependent use')
