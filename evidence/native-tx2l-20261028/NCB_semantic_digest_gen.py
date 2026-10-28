from NCB_generate import *
p='crates/aspis-r1-cost-probe/src/r1_wire.rs'
src=subprocess.check_output(['git','show','4bb3b3f5:'+p],text=True)
# Fill the observer after inspecting the exact public signature.
(E/'NCB_SEMANTIC_DIGEST_SOURCE.txt').write_text(src[src.index('pub struct SemanticTranscript'):src.index('pub struct SemanticTranscript')+3300])
