from pathlib import Path
import re,json,hashlib
repo=Path('/Users/dominic/ZK/.worktrees/100bit-spend-path')
p=repo/'docs/research/100bit-spend-path-20261013/evidence/terminal-indexed-source-candidate-20261016/Funs.lean'
s=p.read_text();name='pool_v1.pair_forest_semantic_terminal.public_digest_lanes'
a=re.search(r'\bdef '+re.escape(name)+r'\s',s).start();start=s.index('  let digests :=',a);end=s.index('  let (digests5, source) ←',start)
raw=s[start:end];old='pool_v1.pair_forest_semantic_terminal.add_digest_binding';new='AspisR1TerminalDigestBindingCandidate.add_digest_binding'
body=raw.replace(old,new)
assert body.replace(new,old)==raw
out=Path('/tmp/DigestFixedPrefixSource.lean')
out.write_text('''import DigestFixedPrefix

/-! Exact initial straight-line cut of the sealed candidate public_digest_lanes.
The sole source-body renaming is the already-proved binding helper owner. -/
set_option autoImplicit false
namespace AspisR1.DigestFixedPrefix.Source
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

/-- Exact source cut; the enclosing loop and suffix are deliberately excluded. -/
def exactPrefix
    (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
    (openings : state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : pool_v1.pair_forest_copy_terminal.Selectors) :
    Result (Array field.QM31 8#usize) := do
'''+body+'''  ok digests4

private theorem result_right_identity {α : Type} (x : Result α) :
    (do let y ← x; Result.ok y) = x := by
  cases x <;> rfl

/-- Factoring the repeated fragment does not change prefix execution or errors. -/
theorem exactPrefix_eq_factored
    (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
    (openings : state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : pool_v1.pair_forest_copy_terminal.Selectors) :
    exactPrefix public1 openings selectors =
      AspisR1.DigestFixedPrefix.fixedPrefix public1 openings.z selectors := by
  simp only [exactPrefix, AspisR1.DigestFixedPrefix.fixedPrefix,
    AspisR1.DigestFixedBinding.bindBlock, AspisR1.DigestFixedPrefix.zero, bind_assoc_eq,
    bind_tc_ok, result_right_identity]
  all_goals rfl

#print axioms exactPrefix_eq_factored
end AspisR1.DigestFixedPrefix.Source
''')
Path('/tmp/DigestFixedPrefixSource.manifest.json').write_text(json.dumps({'raw_source':str(p.relative_to(repo)),'raw_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'declaration':name,'cut_start_byte':len(s[:start].encode()),'cut_end_byte':len(s[:end].encode()),'raw_cut_sha256':hashlib.sha256(raw.encode()).hexdigest(),'substitutions':{old:new},'inverse_check':True,'added_continuation':'  ok digests4\n','output_sha256':hashlib.sha256(out.read_bytes()).hexdigest()},indent=2)+'\n')
print(hashlib.sha256(out.read_bytes()).hexdigest())
