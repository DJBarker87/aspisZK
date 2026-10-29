from pathlib import Path
L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z')
for j in range(4):
 name=f'PV_RunJoin_R24Residue{j}_54';eq=(L/f'PV_RunJoin_R24Equation{j}_54.lean').read_text();bounds=eq.split(' := by\n',1)[1].split('  have hsquare')[0]
 s=f'''import R1Z.PV_RunJoin_R24Equation{j}_54
import R1Z.PV_RunJoin_R24Reduce54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.{name}
open PV_RunJoin_CircleNeutralShape53 PV_RunJoin_CircleNeutralR24Word53
abbrev Q := (U32 × U32) × (U32 × U32)
theorem complete (left right : Q) (hl : QC left) (hr : QC right)
    (u v : Nat) (hu : u<6442450941) (hv : v<6442450941) :
    ∃ y, PV_RunJoin_R24Cell{j}_54.cell left right (word u) (word v)=ok y ∧
      Canon y ∧ y.val=PV_RunJoin_R24Equation{j}_54.accumulator left right u v % 2147483647 := by
'''+bounds+f'''  have hn : PV_RunJoin_R24Equation{j}_54.accumulator left right u v<18446744073709551616 := by
    unfold PV_RunJoin_R24Equation{j}_54.accumulator
    omega
  obtain ⟨y,hy,hc,hv⟩ := PV_RunJoin_R24Reduce54.complete _ hn
  exact ⟨y,(PV_RunJoin_R24Equation{j}_54.complete left right hl hr u v hu hv).trans hy,hc,hv⟩
#print axioms complete
end R1Z.{name}
''';(L/(name+'.lean')).write_text(s)
