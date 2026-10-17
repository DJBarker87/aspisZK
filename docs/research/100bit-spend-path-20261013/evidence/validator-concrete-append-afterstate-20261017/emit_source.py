from pathlib import Path
import re,hashlib,json,argparse
ap=argparse.ArgumentParser();ap.add_argument("--repo",type=Path,required=True);ap.add_argument("--output",type=Path,required=True);ap.add_argument("--check",action="store_true");args=ap.parse_args()
repo=args.repo;p=repo/'docs/research/100bit-spend-path-20261013';raw=(p/'evidence/terminal-indexed-source-candidate-20261016/Funs.lean').read_text();val=(p/'lean/extracted-terminal-validator-20261016/AspisR1TerminalValidator/Funs.lean').read_text()
def block(s,pattern):
 m=re.search(pattern,s);assert m,pattern;return s[m.start():s.index('\n/--',m.start())].strip()+'\n'
option_eq=block(val,r'@\[rust_fun\s+"core::option::\{core::cmp::PartialEq')
option_impl=block(raw,r'@\[reducible, rust_trait_impl\s+"core::cmp::PartialEq<core::option::Option')
constants=[block(raw,pat) for pat in [r'@\[global_simps, irreducible\]\s+def pool_v1\.format\.POOL_V1_TREE_DEPTH\b',r'@\[global_simps, irreducible\]\s+def pool_v1\.pair_tree_profile\.POOL_V1_PAIR_TREE_DEPTH\b',r'@\[global_simps, irreducible\]\s+def pool_v1\.pair_tree_profile\.POOL_V1_PAIR_CAPACITY\b']]
flat=block(raw,r'def pool_v1\.pair_forest_semantic_terminal\.validate_transition\b');original=flat
old='''            let i1 ←
              core.num.U64.trailing_ones
                public1.transition.live_snapshot.next_pair_index
            let i2 ← lift (UScalar.cast .Usize i1)
            let carry ← core.cmp.min core.cmp.OrdUsize i2 20#usize'''
new='''            let carry ← AspisBoundedControl.bounded_carry
              public1.transition.live_snapshot.next_pair_index'''
assert old in flat;flat=flat.replace(old,new)
owner_map={'pool_v1.pair_forest_semantic_terminal.SemanticPublic':'AspisR1TerminalValidateTransitionCandidate.EntryPublic','pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1.InvalidAppendTransition':'AspisR1TerminalValidateTransitionCandidate.EntryInvalid','pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1':'AspisR1TerminalValidateTransitionCandidate.EntryError','pool_v1.pair_forest_semantic_terminal.validate_transition_loop':'AspisR1TerminalValidateTransitionCandidate.validate_transition_loop'}
for a,b in owner_map.items():flat=flat.replace(a,b)
text='''import TerminalValidateTransitionEntryCarry
import Aeneas.Tactic.RustAttributes
import AspisR1TerminalValidator.FunsExternal

/-! Concrete ordered validator, sharing the proved loop/public/error owners.
The carry suffix is the adopted production bounded-carry migration. -/
set_option autoImplicit false
namespace AspisR1.ValidateTransitionConcreteSource
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open scoped AspisR1TerminalValidator

'''+option_eq+'\n'+option_impl+'\n'+'\n'.join(constants)+'\n'+flat+'\nend AspisR1.ValidateTransitionConcreteSource\n'
out=args.output/'ValidateTransitionConcreteSource.lean'
if args.check:assert out.read_text()==text
else:out.parent.mkdir(parents=True,exist_ok=True);out.write_text(text)
manifest={'raw_funs_sha256':hashlib.sha256(raw.encode()).hexdigest(),'option_eq_extracted_validator_sha256':hashlib.sha256(val.encode()).hexdigest(),'original_flat_block_sha256':hashlib.sha256(original.encode()).hexdigest(),'mapped_flat_block_sha256':hashlib.sha256(flat.encode()).hexdigest(),'source_sha256':hashlib.sha256(text.encode()).hexdigest(),'owner_map':owner_map,'carry_replacement':{'old':old,'new':new},'scope':'Shared nominal owners plus explicit adopted bounded-carry source migration. Concrete original capacity and extracted Option implementation retained. Production/runtime correspondence remains a separate obligation.'}
manifest['option_discriminant_reused_source_sha256']=hashlib.sha256((p/'lean/extracted-terminal-validator-20261016/AspisR1TerminalValidator/FunsExternal.lean').read_bytes()).hexdigest()
manifest['production_semantic_source_sha256']=hashlib.sha256((repo/'crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs').read_bytes()).hexdigest()
manifest_text=json.dumps(manifest,indent=2)+'\n'
mp=args.output/'manifest.json'
if args.check:assert mp.read_text()==manifest_text
else:mp.write_text(manifest_text)
print(manifest['source_sha256'])
