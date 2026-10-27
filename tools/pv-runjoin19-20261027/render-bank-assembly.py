from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
def cell(b,w):
 if b<4:j=b
 elif b<25:j=b+2
 elif b<27:j=b-21
 elif b<30:
  if w:return 'PV_RunJoin_BankZero19.certificate'
  j=b+3
 elif b<33:j=b+(6 if w else 3)
 elif b==33:j=40 if w else 39
 elif b<54:j=b+(27 if w else 7)
 else:j=b-27
 return f'PV_RunJoin_BankCell{j:02}19.certificate'
s=''.join(f'import R1Z.PV_RunJoin_BankCells{start:02}19\n' for start in range(0,81,9))+'import R1Z.PV_RunJoin_BankZero19\n'
s+='''set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FixtureBanks19
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1 PV_Src_PortSboxStep
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
'''
for w,name in [(False,'transfer'),(True,'withdrawal')]:
 s+=f'def {name}Certificate (b : Nat) : PV_RunJoin_BankCertificate19.Certificate := match b with\n'
 s+=''.join(f'  | {b} => {cell(b,w)}\n' for b in range(57))+f'  | _ => {cell(0,w)}\n'
s+='''def certificate (withdrawal : Bool) (b : Nat) : PV_RunJoin_BankCertificate19.Certificate :=
  if withdrawal then withdrawalCertificate b else transferCertificate b

/-- The 112 path/auxiliary rows are arbitrary: this theorem validates only
Poseidon rows. Identification with the actual Parts producer is separate. -/
def data (withdrawal : Bool) (tail : Nat → State) (b row : Nat) : State :=
  if b < 57 then (certificate withdrawal b).row row else tail ((b-57)*16+row)

def banks (withdrawal : Bool) (tail : Nat → State) : pair_forest_copy_builder.CopyBanks :=
  PV_RunJoin_BankTable19.banks (PV_RunJoin_BankTable19.cells (data withdrawal tail))
'''
for w,name in [(False,'transfer'),(True,'withdrawal')]:
 boolname=str(w).lower()
 for b in range(57):
  s+=f'''theorem {name}_block{b:02} (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks {boolname} tail) {b}#usize) {b}#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data {boolname} tail) {cell(b,w)} {b}#usize (by decide)
  intro row hr
  rfl
#print axioms {name}_block{b:02}
'''
 s+=f'''theorem {name}_blocks (tail : Nat → State) (b : Usize) (hb : b.val < 57) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks {boolname} tail) b) b = ok (.Ok ()) := by
  apply PV_RunJoin_BankTable19.bounded 57 (by decide) _ _ b hb
  intro j
  fin_cases j
'''+''.join(f'  · exact {name}_block{b:02} tail\n' for b in range(57))
 s+=f'''#print axioms {name}_blocks
theorem {name}_rows (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_rows (banks {boolname} tail) = ok (.Ok ()) :=
  PV_RunJoin_BankAggregate18.rows _ ({name}_blocks tail)
#print axioms {name}_rows
'''
s+='end R1Z.PV_RunJoin_FixtureBanks19\n';p=L/'PV_RunJoin_FixtureBanks19.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
print('114 named block certificates; two 57-block compositions; arbitrary path/aux tail; source identification remains open')
