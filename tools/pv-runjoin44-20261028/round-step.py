from pathlib import Path
p=Path('docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitRoundStep48.lean');s=p.read_text();a=s.index('attribute [local irreducible]');s=s[a:];s=s.replace('sourceArray source value','sourceArray source value')
s=s.replace('theorem step (q w xs','theorem step (ops : ExternalFuns) (count : Usize) (q w xs')
s=s.replace('(d s t : Usize) (hd : d.val < 256)', '(d s t : Usize) (hd : d.val < 256) (size : 4*d.val + 4 ≤ count.val)')
s=s.replace('round_step (sourceArray 1024#usize q) (sourceArray 1024#usize w)\n        (sourceArray 7#usize xs) d s t=ok (sourceArray 7#usize ys)', '@ProverRwFull.prover.round_loop0_loop0_loop0.body _ (ProverRwP6BodyCandidate.selected ops)\n        (Array.to_slice (array count q)) (Array.to_slice (array count w)) d s (array 7#usize xs) t=\n        ok (.cont (array 7#usize ys,Usize.wrapping_add t 1#usize))')
s=s.replace('· rw [round_step,hp]\n    simp only [bind_tc_ok,lift]\n    rw [index _ _ _ (by rw [hidx];omega),index _ _ _ (by rw [hqidx];omega),\n      index _ _ _ (by rw [hwidx];omega)]\n    simp only [hidx,hqidx,hwidx,hm,hz,bind_tc_ok]\n    rw [ProverCommitWideArray48.update _ _ _ (by rw [hidx];omega)]\n    simp only [hidx]\n    rfl', '''· unfold ProverRwFull.prover.round_loop0_loop0_loop0.body
    simp only [show t < 4#usize from ht,↓reduceIte,ProverRwFull.weights.PERM,hp,bind_tc_ok,lift]
    unfold array
    rw [ProverCommitArray49.index 7#usize _ _ (by rw [hidx];omega)]
    rw [PV_RunJoin_Vector44.read count _ _ (by rw [hqidx];omega),
      PV_RunJoin_Vector44.read count _ _ (by rw [hwidx];omega)]
    simp only [hidx,hqidx,hwidx,bind_tc_ok,
      PV_RunJoin_WideArithmetic44.mul ops _ _ _ hm,
      PV_RunJoin_WideArithmetic44.add ops _ _ _ hz]
    rw [ProverCommitArray49.update 7#usize _ _ (by rw [hidx];omega)]
    simp only [hidx,bind_tc_ok]
    congr 2
    apply congrArg (ProverCommitArray49.array 7#usize)
    funext k
    by_cases h : k = s.val+p.val
    · subst k;simp only [ys,Function.update_self]
    · simp only [ys,Function.update_of_ne h]''')
s=s.replace('#print axioms permutation\n','').replace('end R1Z.ProverCommitRoundStep48','end R1Z.PV_RunJoin_RoundStepValue44')
s='''import R1Z.ProverCommitRoundStep48
import R1Z.PV_RunJoin_FourChildren44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RoundStepValue44
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitWideOps48 ProverCommitMix48 PV_RunJoin_WideArithmetic44
open ProverCommitRoundStep48 (perm permutation)
open PV_RunJoin_FoldCell44 (array)
variable [ExternalTypes]
'''+s
Path('docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_RoundStepValue44.lean').write_text(s)
