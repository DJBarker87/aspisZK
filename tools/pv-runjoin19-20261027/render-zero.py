from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s='''import R1Z.PV_RunJoin_IndexedPair19
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ValidatorZero19
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
abbrev CS := {s : State // Canonical s}

theorem total (s : CS) (r : Fin 22) : ∃ out : State,
    poseidon2.apply_round_by_index s.val (Usize.ofNatCore r.val (by have := r.isLt;scalar_tac)) = ok (some (),out) ∧ Canonical out := by
  obtain ⟨out,ho,_⟩ := apply_round_lift (K := PV_RunJoin_FixtureRecords.M) s.val
    (Usize.ofNatCore r.val (by have := r.isLt;scalar_tac)) (by simpa using r.isLt)
  refine ⟨out,?_,fun j => apply_round_canon _ _ out ho j.val j.isLt⟩
  rw [PV_RunJoin_IndexedCopy19.source s.val s.property r,ho]
  rfl
#print axioms total

def next (s : CS) (r : Fin 22) : CS := ⟨Classical.choose (total s r),(Classical.choose_spec (total s r)).2⟩
theorem next_eq (s : CS) (r : Fin 22) :
    poseidon2.apply_round_by_index s.val (Usize.ofNatCore r.val (by have := r.isLt;scalar_tac)) = ok (some (),(next s r).val) :=
  (Classical.choose_spec (total s r)).1
#print axioms next_eq

def zero : CS := ⟨Array.repeat 16#usize 0#u32,by intro j; fin_cases j <;> decide⟩
theorem leading_total : ∃ out : State, poseidon2.external_linear_lazy zero.val = ok out ∧ Canonical out := by
  obtain ⟨out,ho,hc,_⟩ := PV_Src_ExternalModel.source (K := PV_RunJoin_FixtureRecords.M) zero.val
  exact ⟨out,by rw [PV_Src_ExternalReference.call_eq];exact ho,hc⟩
#print axioms leading_total

def s0 : State := zero.val
def lead : CS := ⟨Classical.choose leading_total,(Classical.choose_spec leading_total).2⟩
def s1 : State := lead.val
theorem external : poseidon2.external_linear_lazy s0 = ok s1 := (Classical.choose_spec leading_total).1
#print axioms external
'''
for r in range(22):
 prev='lead' if r==0 else f'c{r+1}'
 s+=f'''def c{r+2} : CS := next {prev} ⟨{r},by decide⟩
def s{r+2} : State := c{r+2}.val
theorem step{r} : poseidon2.apply_round_by_index s{r+1} {r}#usize = ok (some (),s{r+2}) := next_eq {prev} ⟨{r},by decide⟩
#print axioms step{r}
'''
# reuse exactly the preflight-checked pair transport, with its local source names
base=(L/'PV_RunJoin_ValidatorCell0019.lean').read_text();s+=base[base.index('theorem pair0'):base.rindex('end R1Z.')]
s+='end R1Z.PV_RunJoin_ValidatorZero19\n';p=L/'PV_RunJoin_ValidatorZero19.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
