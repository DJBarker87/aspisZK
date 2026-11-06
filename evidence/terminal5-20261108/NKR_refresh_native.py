from pathlib import Path
import json,subprocess,difflib
E=Path(__file__).resolve().parent;P=E/'NKR_K005/sources';rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';patch=''
for filename,oldmods,newmods in [('pair_forest_semantic_terminal.rs',[('NKR_schedule_native','NKR_native'),('NKR_Digest_native','NKR_digest_native')],[('NKR_Term_native','NKR_term_native')]),('pair_forest_copy_terminal.rs',[('NKR_Sum_native','NKR_sum_native')],[('NKR_SumFinish_native','NKR_sum_finish_native'),('NKR_SumPattern_native','NKR_sum_pattern_native')])]:
 root='crates/aspis-statement/src/pool_v1/';path=root+filename;old=subprocess.check_output(['git','show',rev+':'+path],text=True)
 for stem,mod in oldmods:old+='\n#[cfg(kani)]\n#[path="'+stem+'.rs"]\nmod '+mod+';\n'
 new=old
 for stem,mod in newmods:new+='\n#[cfg(kani)]\n#[path="'+stem+'.rs"]\nmod '+mod+';\n'
 patch+=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
 for stem,_ in oldmods+newmods:
  path=root+stem+'.rs';txt=stem+'.rs.txt';old=(P/txt).read_text() if (P/txt).exists() else '';new=(E/txt).read_text()
  patch+=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+path if old else '/dev/null',tofile='b/'+path))
(E/'NKR_UPDATE2.patch').write_text(patch)
print('Incremental private scratch update produced from retained K005 sources')
