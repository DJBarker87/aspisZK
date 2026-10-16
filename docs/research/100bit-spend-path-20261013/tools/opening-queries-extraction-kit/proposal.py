#!/usr/bin/env python3
"""Review-only patch and byte/order audit. Never applies or probes it."""
from pathlib import Path
import difflib,hashlib,json,subprocess
R=Path(__file__).resolve().parents[5];HERE=Path(__file__).resolve().parent;REV='96aad8ef209cb69d7667ab5d8728bd4584a86d16';P='crates/aspis-r1-cost-probe/src/transcript.rs';sha=lambda b:hashlib.sha256(b).hexdigest()
old=subprocess.check_output(['git','-C',str(R),'show',REV+':'+P]).decode();loop='''        for k in 0..8 {
            blocks[k]=self.hash.digest(&[&state,&[1]]);
            advances[k]=self.hash.digest(&[&state,&[2]]);state=advances[k];
        }
''';assert old.count(loop)==1
inner=loop.splitlines(keepends=True)[1:-1];blocks=[]
for i in range(8):
 block=''.join(inner).replace('[k]',f'[{i}]');blocks.append(''.join(line[4:] for line in block.splitlines(keepends=True)))
new=old.replace(loop,''.join(blocks),1);before,after=old.split(loop);assert new==before+''.join(blocks)+after
patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+P,tofile='b/'+P)).encode();out=HERE/'proposal-eight-pairs';out.mkdir(exist_ok=True);(out/'proposal.patch').write_bytes(patch)
audit={'status':'REVIEW_ONLY_NOT_APPLIED_NOT_PROBED','source_revision':REV,'path':P,'old_file_sha256':sha(old.encode()),'proposed_file_sha256':sha(new.encode()),'patch_sha256':sha(patch),'unchanged_prefix_sha256':sha(before.encode()),'unchanged_suffix_sha256':sha(after.encode()),'old_loop_sha256':sha(loop.encode()),'proposed_sequence_sha256':sha(''.join(blocks).encode()),'sole_adapter':'Expand k in0..8 into eight exact copies of its body, substitute each[k] by literal[0]..[7], remove four indentation spaces. No other source change.','ordered_digest_tags':[tag for i in range(8) for tag in [1,2]],'iteration_audit':[{'k':i,'expanded_body_sha256':sha(b.encode()),'block_state':'previous advances[k-1], or initial absorbed self.state for k0','advance_state':'same pre-read state as paired block; local state then assigned advances[k]'}for i,b in enumerate(blocks)],'semantics_argument':'Fixed finite loop expansion retains exactly8iterations in increasingindex order. Eachiteration performs readtag1,advancetag2 using the same incoming localstate, then state=advances[k]. Induction on k preserves both arrays and localstate. The unchanged suffix still calls queries_from_pairs and assigns its RETURNED state to self.state; it does not assign the final localadvance directly. No allocation/API/domain/error/trace changes. This is a proposed source equivalence argument, not a checked extraction/proof result.','remaining_risk':'The unchanged q.iter().enumerate trace loop has not yet been reached by Aeneas; a second extractor blocker is possible. No automatic follow-on rewrite is authorized.'};(out/'audit.json').write_text(json.dumps(audit,indent=2)+'\n');print(json.dumps({'status':audit['status'],'patch_sha256':sha(patch)}))
