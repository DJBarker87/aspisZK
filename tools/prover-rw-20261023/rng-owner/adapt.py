from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent;R=D.parents[2]
f=(D/'generated/Funs.lean.txt').read_text()
f=f[f.index('/-- [prover_rw_rng_owner::{impl core::convert::From'):]
out='''import R1Z.ProverRwRngEmission
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace ProverRwRng
variable [ErasureFns]
'''+f
p=R/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngOwnerEmission.lean';p.write_text(out)
# Common emitted declarations reuse the exact prior emission, checked bytewise
# after removing crate-name/doc-source-span differences only.
(D/'adaptation.json').write_text(json.dumps({'raw_sha256':hashlib.sha256((D/'generated/Funs.lean.txt').read_bytes()).hexdigest(),'output_sha256':hashlib.sha256(out.encode()).hexdigest(),'output':str(p.relative_to(R)),'changes':['import common type/helper/value installation from normalized ProverRwRngEmission','retain From<u8>, borrowed Tape.draw, complete borrowed old body/loop/owner, old_owner verbatim','strip generated resource overrides outside retained declaration region'],'no_new_external_axioms':True},indent=2)+'\n')
