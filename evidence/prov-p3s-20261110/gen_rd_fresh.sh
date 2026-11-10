#!/bin/bash
# extracts the frozen read_checkpoint_* text (PCVU_E002) into PCVU_Rd_fresh.inc with the two externals as parameters
cd "$(dirname "$0")"
python3 - <<'EOF'
import re
t=open('PCVU_E002_emitted/raw/PCVU_rdckpt/Funs.lean').read()
i=t.index("/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::Reader<'a>}::raw]")
b=t[i:t.index('end PCVU_rdckpt')]
FLE="(fle : Slice Std.U8 → Result (Option aspis_core.field.QM31))"
INTO="(into_iter : alloc.vec.Vec aspis_core.field.QM31 → Result ((core.slice.iter.IterMut aspis_core.field.QM31) × (core.slice.iter.IterMut aspis_core.field.QM31 → alloc.vec.Vec aspis_core.field.QM31)))"
# definitions: add fle parameter
b=b.replace("def verifier.Reader.k\n  (self","def verifier.Reader.k\n  %s\n  (self"%FLE)
b=b.replace("def verifier.read_checkpoint_weights_loop.body\n  (bytes","def verifier.read_checkpoint_weights_loop.body\n  %s (bytes"%FLE)
b=b.replace("def verifier.read_checkpoint_weights_loop\n  (iter","def verifier.read_checkpoint_weights_loop\n  %s (iter"%FLE)
b=b.replace("def verifier.read_checkpoint_weights\n  (bytes","def verifier.read_checkpoint_weights\n  %s %s (bytes"%(FLE,INTO))
b=b.replace("def verifier.read_checkpoint_semantic_alpha\n  (bytes","def verifier.read_checkpoint_semantic_alpha\n  %s (bytes"%FLE)
# calls
b=b.replace("aspis_core.field.QM31.from_le_bytes s","fle s")
b=b.replace("core.option.Option.ok_or o verifier.Error.Checkpoint","core.option.Option.ok_or o AdapterRw.aspis_r1_cost_probe.verifier.Error.Checkpoint")
b=re.sub(r"verifier\.Reader\.k (?!fle)(?=[\{r])","verifier.Reader.k fle ",b)
b=b.replace("verifier.Reader.k fle \n","verifier.Reader.k fle\n")
b=b.replace("verifier.read_checkpoint_weights_loop.body\n      bytes iter1","verifier.read_checkpoint_weights_loop.body\n      fle bytes iter1")
b=b.replace("verifier.read_checkpoint_weights_loop iter (fun im => im) bytes at1","verifier.read_checkpoint_weights_loop fle iter (fun im => im) bytes at1")
b=re.sub(r"MutAVec\.Insts\.CoreIterTraitsCollectIntoIteratorMutATIterMut\.into_iter\s+Global weights","into_iter weights",b)
open('PCVU_Rd_fresh.inc','w').write(b)
print(b.count('fle'),b.count('into_iter'))
EOF
