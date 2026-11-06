from NKP_box_tail import *
import lzma

def attempt(a,kind,field,mode):
 text,edits,mod=shape(kind,field,mode)
 (E/(a+'.patch')).write_text('--- /dev/null\n+++ b/'+mod+'.rs\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+line for line in text.splitlines(True)))
 (E/(a+'_CUT.json')).write_text(json.dumps(dict(source=P,kind=kind,field=field,mode=mode,oracle='full arbitrary typed child Result at unchanged bytes',modifies=[],edits=edits,instrumented_sha256=sha(edits[0][1].encode()),reference='raw = actual source child invocation at SAME immutable bytes',input_length='0..33 representative; tail does not read bytes'),indent=1)+'\n')
 rc=submit(a,'r1_pool_adapter::'+mod+'::returned',P,mod,text,mode,edits=edits)
 log=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 if mode=='positive':assert rc['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in log
 else:assert rc['exit_status']!=0 and 'VERIFICATION:- FAILED' in log and 'timed out' not in log and 'Failed Checks: "actual wrapper returned field/error at SAME raw decoder call"' in log
 return rc
if __name__=='__main__':
 # K003 already has the exact expected failing check; parser repaired, not rerun.
 assert 'Failed Checks: "actual wrapper returned field/error at SAME raw decoder call"' in lzma.decompress((E/'NKP_K003/stdout.log.xz').read_bytes()).decode()
 n=4
 for kind,fields in [('checkpoint',range(1,6)),('master',range(14))]:
  for field in fields:
   for mode in ['positive','inverse']:
    attempt(f'NKP_K{n:03}',kind,field,mode);n+=1
 print('BOX_STAGE_COMPLETE',flush=True)
