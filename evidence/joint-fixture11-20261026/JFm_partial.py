from pathlib import Path
import sys
P=Path(__file__).resolve().parent;R=P.parents[1];v=lambda i:f'JFm_Coordinates.value{i:02}'
s='''import JFm_Coordinates
import JFm_HornerAlpha
import JFr_RealRounds
set_option autoImplicit false
namespace AspisR1.JFm_PartialAlpha
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1ExtractedRoundChildren
'''
zero='aspis_core.field.QM31.ZERO'
s+='def a00 : Array MainQM 10#usize := Array.repeat 10#usize aspis_core.field.QM31.ZERO\n'
for n in range(1,11):s+=f'def a{n:02} : Array MainQM 10#usize := ⟨['+','.join(v(i+15) if i<n else zero for i in range(10))+'],by rfl⟩\n'
s+='theorem full : a10=JFr_Round00.challenges := by rfl\n#print axioms full\n'
for r in range(10):
 s+=f'''theorem update{r:02} : Array.update a{r:02} {r}#usize {v(15+r)}=ok a{r+1:02} := by rfl
#print axioms update{r:02}
theorem horner{r:02} : AspisR1SemanticCallExtraction.r1_semantic.semantic_value JFr_Data{r:02}.p
    (mainAlphaArrayToGen a{r+1:02}) {r}#usize=ok JFr_Data{r:02}.output := by
  have joined := JFr_HornerTrace.append JFr_Horner{r:02}_0.trace JFr_Horner{r:02}_1.trace
  have moved := JFm_HornerAlpha.transport (b := mainAlphaArrayToGen a{r+1:02}) joined (by rfl)
  have zero : JFr_Horner{r:02}_0.initial=AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO := by
    unfold JFr_Horner{r:02}_0.initial JFr_WordArithmetic.q AspisR1SemanticCallExtraction.aspis_core.field.QM31.ZERO
    rfl
  have last : JFr_Horner{r:02}_1.final=JFr_Data{r:02}.output := rfl
  rw [zero,last] at moved
  exact JFr_HornerTrace.source moved (by change ¬(0:Nat)>0;omega)
#print axioms horner{r:02}
theorem value{r:02} : generatedMainValue JFr_Round{r:02}.polynomial a{r+1:02} {r}#usize=
    ok (genToMain JFr_Data{r:02}.output) := by
  unfold generatedMainValue AspisR1SemanticCallExtraction.r1_semantic.semantic_value_entry
  have same : mainArrayToGen JFr_Round{r:02}.polynomial=JFr_Data{r:02}.p := rfl
  rw [same,horner{r:02}]
  rfl
#print axioms value{r:02}
'''
s+='end AspisR1.JFm_PartialAlpha\n';f=R/'lean/JFm_PartialAlpha.lean'
if '--check' in sys.argv:assert f.read_text()==s
else:f.write_text(s)
