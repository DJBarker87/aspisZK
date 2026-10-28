from NCB_generate import *
p='crates/aspis-r1-cost-probe/src/transcript.rs';s=current(p)
# Keep observation harness in the original module to reuse its exact observer.
needle='\n}\n';at=s.rfind(needle);assert at>=0
text=''
for name in ['absorb','block']:
 start=s.index(' #[kani::proof] #[kani::unwind(512)]',s.index('fn '+name+'(')-1200) if False else s.rfind('#[kani::proof]',0,s.index('fn '+name+'(){',s.index('mod NCB_digest_calls')))
 m=s.index('fn '+name+'(){',start);brace=s.index('{',m);depth=1;end=brace+1
 while depth:depth+=(s[end]=='{')-(s[end]=='}');end+=1
 original=s[start:end]
 assert 'payload:[u8;64]' in original
 new=original.replace('fn '+name+'(){','fn '+name+'_full_bound(){').replace('payload:[u8;64]','payload:[u8;57607]').replace('n<=64','n<=57607')
 text+='\n'+new+'\n'
t=s[:at]+text+s[at:]
(E/'NCB_transcript_large.patch').write_text(''.join(difflib.unified_diff(s.splitlines(True),t.splitlines(True),fromfile='a/'+p,tofile='b/'+p)))
