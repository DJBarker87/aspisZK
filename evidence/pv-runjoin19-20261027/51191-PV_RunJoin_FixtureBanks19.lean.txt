import R1Z.PV_RunJoin_BankCells0019
import R1Z.PV_RunJoin_BankCells0919
import R1Z.PV_RunJoin_BankCells1819
import R1Z.PV_RunJoin_BankCells2719
import R1Z.PV_RunJoin_BankCells3619
import R1Z.PV_RunJoin_BankCells4519
import R1Z.PV_RunJoin_BankCells5419
import R1Z.PV_RunJoin_BankCells6319
import R1Z.PV_RunJoin_BankCells7219
import R1Z.PV_RunJoin_BankZero19
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FixtureBanks19
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1 PV_Src_PortSboxStep
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
def transferCertificate (b : Nat) : PV_RunJoin_BankCertificate19.Certificate := match b with
  | 0 => PV_RunJoin_BankCell0019.certificate
  | 1 => PV_RunJoin_BankCell0119.certificate
  | 2 => PV_RunJoin_BankCell0219.certificate
  | 3 => PV_RunJoin_BankCell0319.certificate
  | 4 => PV_RunJoin_BankCell0619.certificate
  | 5 => PV_RunJoin_BankCell0719.certificate
  | 6 => PV_RunJoin_BankCell0819.certificate
  | 7 => PV_RunJoin_BankCell0919.certificate
  | 8 => PV_RunJoin_BankCell1019.certificate
  | 9 => PV_RunJoin_BankCell1119.certificate
  | 10 => PV_RunJoin_BankCell1219.certificate
  | 11 => PV_RunJoin_BankCell1319.certificate
  | 12 => PV_RunJoin_BankCell1419.certificate
  | 13 => PV_RunJoin_BankCell1519.certificate
  | 14 => PV_RunJoin_BankCell1619.certificate
  | 15 => PV_RunJoin_BankCell1719.certificate
  | 16 => PV_RunJoin_BankCell1819.certificate
  | 17 => PV_RunJoin_BankCell1919.certificate
  | 18 => PV_RunJoin_BankCell2019.certificate
  | 19 => PV_RunJoin_BankCell2119.certificate
  | 20 => PV_RunJoin_BankCell2219.certificate
  | 21 => PV_RunJoin_BankCell2319.certificate
  | 22 => PV_RunJoin_BankCell2419.certificate
  | 23 => PV_RunJoin_BankCell2519.certificate
  | 24 => PV_RunJoin_BankCell2619.certificate
  | 25 => PV_RunJoin_BankCell0419.certificate
  | 26 => PV_RunJoin_BankCell0519.certificate
  | 27 => PV_RunJoin_BankCell3019.certificate
  | 28 => PV_RunJoin_BankCell3119.certificate
  | 29 => PV_RunJoin_BankCell3219.certificate
  | 30 => PV_RunJoin_BankCell3319.certificate
  | 31 => PV_RunJoin_BankCell3419.certificate
  | 32 => PV_RunJoin_BankCell3519.certificate
  | 33 => PV_RunJoin_BankCell3919.certificate
  | 34 => PV_RunJoin_BankCell4119.certificate
  | 35 => PV_RunJoin_BankCell4219.certificate
  | 36 => PV_RunJoin_BankCell4319.certificate
  | 37 => PV_RunJoin_BankCell4419.certificate
  | 38 => PV_RunJoin_BankCell4519.certificate
  | 39 => PV_RunJoin_BankCell4619.certificate
  | 40 => PV_RunJoin_BankCell4719.certificate
  | 41 => PV_RunJoin_BankCell4819.certificate
  | 42 => PV_RunJoin_BankCell4919.certificate
  | 43 => PV_RunJoin_BankCell5019.certificate
  | 44 => PV_RunJoin_BankCell5119.certificate
  | 45 => PV_RunJoin_BankCell5219.certificate
  | 46 => PV_RunJoin_BankCell5319.certificate
  | 47 => PV_RunJoin_BankCell5419.certificate
  | 48 => PV_RunJoin_BankCell5519.certificate
  | 49 => PV_RunJoin_BankCell5619.certificate
  | 50 => PV_RunJoin_BankCell5719.certificate
  | 51 => PV_RunJoin_BankCell5819.certificate
  | 52 => PV_RunJoin_BankCell5919.certificate
  | 53 => PV_RunJoin_BankCell6019.certificate
  | 54 => PV_RunJoin_BankCell2719.certificate
  | 55 => PV_RunJoin_BankCell2819.certificate
  | 56 => PV_RunJoin_BankCell2919.certificate
  | _ => PV_RunJoin_BankCell0019.certificate
def withdrawalCertificate (b : Nat) : PV_RunJoin_BankCertificate19.Certificate := match b with
  | 0 => PV_RunJoin_BankCell0019.certificate
  | 1 => PV_RunJoin_BankCell0119.certificate
  | 2 => PV_RunJoin_BankCell0219.certificate
  | 3 => PV_RunJoin_BankCell0319.certificate
  | 4 => PV_RunJoin_BankCell0619.certificate
  | 5 => PV_RunJoin_BankCell0719.certificate
  | 6 => PV_RunJoin_BankCell0819.certificate
  | 7 => PV_RunJoin_BankCell0919.certificate
  | 8 => PV_RunJoin_BankCell1019.certificate
  | 9 => PV_RunJoin_BankCell1119.certificate
  | 10 => PV_RunJoin_BankCell1219.certificate
  | 11 => PV_RunJoin_BankCell1319.certificate
  | 12 => PV_RunJoin_BankCell1419.certificate
  | 13 => PV_RunJoin_BankCell1519.certificate
  | 14 => PV_RunJoin_BankCell1619.certificate
  | 15 => PV_RunJoin_BankCell1719.certificate
  | 16 => PV_RunJoin_BankCell1819.certificate
  | 17 => PV_RunJoin_BankCell1919.certificate
  | 18 => PV_RunJoin_BankCell2019.certificate
  | 19 => PV_RunJoin_BankCell2119.certificate
  | 20 => PV_RunJoin_BankCell2219.certificate
  | 21 => PV_RunJoin_BankCell2319.certificate
  | 22 => PV_RunJoin_BankCell2419.certificate
  | 23 => PV_RunJoin_BankCell2519.certificate
  | 24 => PV_RunJoin_BankCell2619.certificate
  | 25 => PV_RunJoin_BankCell0419.certificate
  | 26 => PV_RunJoin_BankCell0519.certificate
  | 27 => PV_RunJoin_BankZero19.certificate
  | 28 => PV_RunJoin_BankZero19.certificate
  | 29 => PV_RunJoin_BankZero19.certificate
  | 30 => PV_RunJoin_BankCell3619.certificate
  | 31 => PV_RunJoin_BankCell3719.certificate
  | 32 => PV_RunJoin_BankCell3819.certificate
  | 33 => PV_RunJoin_BankCell4019.certificate
  | 34 => PV_RunJoin_BankCell6119.certificate
  | 35 => PV_RunJoin_BankCell6219.certificate
  | 36 => PV_RunJoin_BankCell6319.certificate
  | 37 => PV_RunJoin_BankCell6419.certificate
  | 38 => PV_RunJoin_BankCell6519.certificate
  | 39 => PV_RunJoin_BankCell6619.certificate
  | 40 => PV_RunJoin_BankCell6719.certificate
  | 41 => PV_RunJoin_BankCell6819.certificate
  | 42 => PV_RunJoin_BankCell6919.certificate
  | 43 => PV_RunJoin_BankCell7019.certificate
  | 44 => PV_RunJoin_BankCell7119.certificate
  | 45 => PV_RunJoin_BankCell7219.certificate
  | 46 => PV_RunJoin_BankCell7319.certificate
  | 47 => PV_RunJoin_BankCell7419.certificate
  | 48 => PV_RunJoin_BankCell7519.certificate
  | 49 => PV_RunJoin_BankCell7619.certificate
  | 50 => PV_RunJoin_BankCell7719.certificate
  | 51 => PV_RunJoin_BankCell7819.certificate
  | 52 => PV_RunJoin_BankCell7919.certificate
  | 53 => PV_RunJoin_BankCell8019.certificate
  | 54 => PV_RunJoin_BankCell2719.certificate
  | 55 => PV_RunJoin_BankCell2819.certificate
  | 56 => PV_RunJoin_BankCell2919.certificate
  | _ => PV_RunJoin_BankCell0019.certificate
def certificate (withdrawal : Bool) (b : Nat) : PV_RunJoin_BankCertificate19.Certificate :=
  if withdrawal then withdrawalCertificate b else transferCertificate b

/-- The 112 path/auxiliary rows are arbitrary: this theorem validates only
Poseidon rows. Identification with the actual Parts producer is separate. -/
def data (withdrawal : Bool) (tail : Nat → State) (b row : Nat) : State :=
  if b < 57 then (certificate withdrawal b).row row else tail ((b-57)*16+row)

def banks (withdrawal : Bool) (tail : Nat → State) : pair_forest_copy_builder.CopyBanks :=
  PV_RunJoin_BankTable19.banks (PV_RunJoin_BankTable19.cells (data withdrawal tail))
theorem transfer_block00 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 0#usize) 0#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell0019.certificate 0#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block00
theorem transfer_block01 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 1#usize) 1#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell0119.certificate 1#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block01
theorem transfer_block02 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 2#usize) 2#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell0219.certificate 2#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block02
theorem transfer_block03 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 3#usize) 3#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell0319.certificate 3#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block03
theorem transfer_block04 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 4#usize) 4#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell0619.certificate 4#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block04
theorem transfer_block05 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 5#usize) 5#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell0719.certificate 5#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block05
theorem transfer_block06 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 6#usize) 6#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell0819.certificate 6#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block06
theorem transfer_block07 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 7#usize) 7#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell0919.certificate 7#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block07
theorem transfer_block08 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 8#usize) 8#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell1019.certificate 8#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block08
theorem transfer_block09 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 9#usize) 9#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell1119.certificate 9#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block09
theorem transfer_block10 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 10#usize) 10#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell1219.certificate 10#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block10
theorem transfer_block11 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 11#usize) 11#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell1319.certificate 11#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block11
theorem transfer_block12 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 12#usize) 12#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell1419.certificate 12#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block12
theorem transfer_block13 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 13#usize) 13#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell1519.certificate 13#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block13
theorem transfer_block14 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 14#usize) 14#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell1619.certificate 14#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block14
theorem transfer_block15 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 15#usize) 15#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell1719.certificate 15#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block15
theorem transfer_block16 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 16#usize) 16#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell1819.certificate 16#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block16
theorem transfer_block17 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 17#usize) 17#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell1919.certificate 17#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block17
theorem transfer_block18 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 18#usize) 18#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell2019.certificate 18#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block18
theorem transfer_block19 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 19#usize) 19#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell2119.certificate 19#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block19
theorem transfer_block20 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 20#usize) 20#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell2219.certificate 20#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block20
theorem transfer_block21 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 21#usize) 21#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell2319.certificate 21#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block21
theorem transfer_block22 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 22#usize) 22#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell2419.certificate 22#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block22
theorem transfer_block23 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 23#usize) 23#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell2519.certificate 23#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block23
theorem transfer_block24 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 24#usize) 24#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell2619.certificate 24#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block24
theorem transfer_block25 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 25#usize) 25#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell0419.certificate 25#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block25
theorem transfer_block26 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 26#usize) 26#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell0519.certificate 26#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block26
theorem transfer_block27 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 27#usize) 27#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell3019.certificate 27#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block27
theorem transfer_block28 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 28#usize) 28#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell3119.certificate 28#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block28
theorem transfer_block29 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 29#usize) 29#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell3219.certificate 29#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block29
theorem transfer_block30 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 30#usize) 30#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell3319.certificate 30#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block30
theorem transfer_block31 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 31#usize) 31#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell3419.certificate 31#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block31
theorem transfer_block32 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 32#usize) 32#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell3519.certificate 32#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block32
theorem transfer_block33 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 33#usize) 33#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell3919.certificate 33#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block33
theorem transfer_block34 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 34#usize) 34#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell4119.certificate 34#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block34
theorem transfer_block35 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 35#usize) 35#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell4219.certificate 35#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block35
theorem transfer_block36 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 36#usize) 36#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell4319.certificate 36#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block36
theorem transfer_block37 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 37#usize) 37#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell4419.certificate 37#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block37
theorem transfer_block38 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 38#usize) 38#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell4519.certificate 38#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block38
theorem transfer_block39 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 39#usize) 39#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell4619.certificate 39#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block39
theorem transfer_block40 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 40#usize) 40#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell4719.certificate 40#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block40
theorem transfer_block41 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 41#usize) 41#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell4819.certificate 41#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block41
theorem transfer_block42 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 42#usize) 42#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell4919.certificate 42#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block42
theorem transfer_block43 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 43#usize) 43#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell5019.certificate 43#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block43
theorem transfer_block44 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 44#usize) 44#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell5119.certificate 44#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block44
theorem transfer_block45 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 45#usize) 45#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell5219.certificate 45#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block45
theorem transfer_block46 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 46#usize) 46#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell5319.certificate 46#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block46
theorem transfer_block47 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 47#usize) 47#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell5419.certificate 47#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block47
theorem transfer_block48 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 48#usize) 48#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell5519.certificate 48#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block48
theorem transfer_block49 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 49#usize) 49#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell5619.certificate 49#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block49
theorem transfer_block50 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 50#usize) 50#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell5719.certificate 50#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block50
theorem transfer_block51 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 51#usize) 51#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell5819.certificate 51#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block51
theorem transfer_block52 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 52#usize) 52#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell5919.certificate 52#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block52
theorem transfer_block53 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 53#usize) 53#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell6019.certificate 53#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block53
theorem transfer_block54 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 54#usize) 54#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell2719.certificate 54#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block54
theorem transfer_block55 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 55#usize) 55#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell2819.certificate 55#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block55
theorem transfer_block56 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) 56#usize) 56#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data false tail) PV_RunJoin_BankCell2919.certificate 56#usize (by decide)
  intro row hr
  rfl
#print axioms transfer_block56
theorem transfer_blocks (tail : Nat → State) (b : Usize) (hb : b.val < 57) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks false tail) b) b = ok (.Ok ()) := by
  apply PV_RunJoin_BankTable19.bounded 57 (by decide) _ _ b hb
  intro j
  fin_cases j
  · exact transfer_block00 tail
  · exact transfer_block01 tail
  · exact transfer_block02 tail
  · exact transfer_block03 tail
  · exact transfer_block04 tail
  · exact transfer_block05 tail
  · exact transfer_block06 tail
  · exact transfer_block07 tail
  · exact transfer_block08 tail
  · exact transfer_block09 tail
  · exact transfer_block10 tail
  · exact transfer_block11 tail
  · exact transfer_block12 tail
  · exact transfer_block13 tail
  · exact transfer_block14 tail
  · exact transfer_block15 tail
  · exact transfer_block16 tail
  · exact transfer_block17 tail
  · exact transfer_block18 tail
  · exact transfer_block19 tail
  · exact transfer_block20 tail
  · exact transfer_block21 tail
  · exact transfer_block22 tail
  · exact transfer_block23 tail
  · exact transfer_block24 tail
  · exact transfer_block25 tail
  · exact transfer_block26 tail
  · exact transfer_block27 tail
  · exact transfer_block28 tail
  · exact transfer_block29 tail
  · exact transfer_block30 tail
  · exact transfer_block31 tail
  · exact transfer_block32 tail
  · exact transfer_block33 tail
  · exact transfer_block34 tail
  · exact transfer_block35 tail
  · exact transfer_block36 tail
  · exact transfer_block37 tail
  · exact transfer_block38 tail
  · exact transfer_block39 tail
  · exact transfer_block40 tail
  · exact transfer_block41 tail
  · exact transfer_block42 tail
  · exact transfer_block43 tail
  · exact transfer_block44 tail
  · exact transfer_block45 tail
  · exact transfer_block46 tail
  · exact transfer_block47 tail
  · exact transfer_block48 tail
  · exact transfer_block49 tail
  · exact transfer_block50 tail
  · exact transfer_block51 tail
  · exact transfer_block52 tail
  · exact transfer_block53 tail
  · exact transfer_block54 tail
  · exact transfer_block55 tail
  · exact transfer_block56 tail
#print axioms transfer_blocks
theorem transfer_rows (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_rows (banks false tail) = ok (.Ok ()) :=
  PV_RunJoin_BankAggregate18.rows _ (transfer_blocks tail)
#print axioms transfer_rows
theorem withdrawal_block00 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 0#usize) 0#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell0019.certificate 0#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block00
theorem withdrawal_block01 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 1#usize) 1#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell0119.certificate 1#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block01
theorem withdrawal_block02 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 2#usize) 2#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell0219.certificate 2#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block02
theorem withdrawal_block03 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 3#usize) 3#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell0319.certificate 3#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block03
theorem withdrawal_block04 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 4#usize) 4#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell0619.certificate 4#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block04
theorem withdrawal_block05 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 5#usize) 5#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell0719.certificate 5#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block05
theorem withdrawal_block06 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 6#usize) 6#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell0819.certificate 6#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block06
theorem withdrawal_block07 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 7#usize) 7#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell0919.certificate 7#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block07
theorem withdrawal_block08 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 8#usize) 8#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell1019.certificate 8#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block08
theorem withdrawal_block09 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 9#usize) 9#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell1119.certificate 9#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block09
theorem withdrawal_block10 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 10#usize) 10#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell1219.certificate 10#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block10
theorem withdrawal_block11 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 11#usize) 11#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell1319.certificate 11#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block11
theorem withdrawal_block12 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 12#usize) 12#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell1419.certificate 12#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block12
theorem withdrawal_block13 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 13#usize) 13#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell1519.certificate 13#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block13
theorem withdrawal_block14 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 14#usize) 14#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell1619.certificate 14#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block14
theorem withdrawal_block15 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 15#usize) 15#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell1719.certificate 15#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block15
theorem withdrawal_block16 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 16#usize) 16#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell1819.certificate 16#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block16
theorem withdrawal_block17 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 17#usize) 17#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell1919.certificate 17#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block17
theorem withdrawal_block18 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 18#usize) 18#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell2019.certificate 18#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block18
theorem withdrawal_block19 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 19#usize) 19#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell2119.certificate 19#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block19
theorem withdrawal_block20 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 20#usize) 20#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell2219.certificate 20#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block20
theorem withdrawal_block21 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 21#usize) 21#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell2319.certificate 21#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block21
theorem withdrawal_block22 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 22#usize) 22#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell2419.certificate 22#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block22
theorem withdrawal_block23 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 23#usize) 23#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell2519.certificate 23#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block23
theorem withdrawal_block24 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 24#usize) 24#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell2619.certificate 24#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block24
theorem withdrawal_block25 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 25#usize) 25#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell0419.certificate 25#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block25
theorem withdrawal_block26 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 26#usize) 26#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell0519.certificate 26#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block26
theorem withdrawal_block27 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 27#usize) 27#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankZero19.certificate 27#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block27
theorem withdrawal_block28 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 28#usize) 28#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankZero19.certificate 28#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block28
theorem withdrawal_block29 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 29#usize) 29#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankZero19.certificate 29#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block29
theorem withdrawal_block30 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 30#usize) 30#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell3619.certificate 30#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block30
theorem withdrawal_block31 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 31#usize) 31#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell3719.certificate 31#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block31
theorem withdrawal_block32 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 32#usize) 32#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell3819.certificate 32#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block32
theorem withdrawal_block33 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 33#usize) 33#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell4019.certificate 33#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block33
theorem withdrawal_block34 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 34#usize) 34#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell6119.certificate 34#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block34
theorem withdrawal_block35 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 35#usize) 35#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell6219.certificate 35#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block35
theorem withdrawal_block36 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 36#usize) 36#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell6319.certificate 36#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block36
theorem withdrawal_block37 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 37#usize) 37#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell6419.certificate 37#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block37
theorem withdrawal_block38 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 38#usize) 38#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell6519.certificate 38#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block38
theorem withdrawal_block39 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 39#usize) 39#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell6619.certificate 39#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block39
theorem withdrawal_block40 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 40#usize) 40#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell6719.certificate 40#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block40
theorem withdrawal_block41 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 41#usize) 41#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell6819.certificate 41#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block41
theorem withdrawal_block42 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 42#usize) 42#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell6919.certificate 42#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block42
theorem withdrawal_block43 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 43#usize) 43#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell7019.certificate 43#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block43
theorem withdrawal_block44 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 44#usize) 44#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell7119.certificate 44#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block44
theorem withdrawal_block45 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 45#usize) 45#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell7219.certificate 45#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block45
theorem withdrawal_block46 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 46#usize) 46#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell7319.certificate 46#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block46
theorem withdrawal_block47 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 47#usize) 47#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell7419.certificate 47#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block47
theorem withdrawal_block48 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 48#usize) 48#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell7519.certificate 48#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block48
theorem withdrawal_block49 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 49#usize) 49#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell7619.certificate 49#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block49
theorem withdrawal_block50 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 50#usize) 50#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell7719.certificate 50#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block50
theorem withdrawal_block51 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 51#usize) 51#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell7819.certificate 51#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block51
theorem withdrawal_block52 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 52#usize) 52#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell7919.certificate 52#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block52
theorem withdrawal_block53 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 53#usize) 53#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell8019.certificate 53#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block53
theorem withdrawal_block54 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 54#usize) 54#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell2719.certificate 54#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block54
theorem withdrawal_block55 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 55#usize) 55#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell2819.certificate 55#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block55
theorem withdrawal_block56 (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) 56#usize) 56#usize = ok (.Ok ()) := by
  apply PV_RunJoin_BankCertificate19.block (data true tail) PV_RunJoin_BankCell2919.certificate 56#usize (by decide)
  intro row hr
  rfl
#print axioms withdrawal_block56
theorem withdrawal_blocks (tail : Nat → State) (b : Usize) (hb : b.val < 57) :
    pair_forest_trace.validate_forest_poseidon_block
      (PV_RunJoin_BankAggregate18.columns (banks true tail) b) b = ok (.Ok ()) := by
  apply PV_RunJoin_BankTable19.bounded 57 (by decide) _ _ b hb
  intro j
  fin_cases j
  · exact withdrawal_block00 tail
  · exact withdrawal_block01 tail
  · exact withdrawal_block02 tail
  · exact withdrawal_block03 tail
  · exact withdrawal_block04 tail
  · exact withdrawal_block05 tail
  · exact withdrawal_block06 tail
  · exact withdrawal_block07 tail
  · exact withdrawal_block08 tail
  · exact withdrawal_block09 tail
  · exact withdrawal_block10 tail
  · exact withdrawal_block11 tail
  · exact withdrawal_block12 tail
  · exact withdrawal_block13 tail
  · exact withdrawal_block14 tail
  · exact withdrawal_block15 tail
  · exact withdrawal_block16 tail
  · exact withdrawal_block17 tail
  · exact withdrawal_block18 tail
  · exact withdrawal_block19 tail
  · exact withdrawal_block20 tail
  · exact withdrawal_block21 tail
  · exact withdrawal_block22 tail
  · exact withdrawal_block23 tail
  · exact withdrawal_block24 tail
  · exact withdrawal_block25 tail
  · exact withdrawal_block26 tail
  · exact withdrawal_block27 tail
  · exact withdrawal_block28 tail
  · exact withdrawal_block29 tail
  · exact withdrawal_block30 tail
  · exact withdrawal_block31 tail
  · exact withdrawal_block32 tail
  · exact withdrawal_block33 tail
  · exact withdrawal_block34 tail
  · exact withdrawal_block35 tail
  · exact withdrawal_block36 tail
  · exact withdrawal_block37 tail
  · exact withdrawal_block38 tail
  · exact withdrawal_block39 tail
  · exact withdrawal_block40 tail
  · exact withdrawal_block41 tail
  · exact withdrawal_block42 tail
  · exact withdrawal_block43 tail
  · exact withdrawal_block44 tail
  · exact withdrawal_block45 tail
  · exact withdrawal_block46 tail
  · exact withdrawal_block47 tail
  · exact withdrawal_block48 tail
  · exact withdrawal_block49 tail
  · exact withdrawal_block50 tail
  · exact withdrawal_block51 tail
  · exact withdrawal_block52 tail
  · exact withdrawal_block53 tail
  · exact withdrawal_block54 tail
  · exact withdrawal_block55 tail
  · exact withdrawal_block56 tail
#print axioms withdrawal_blocks
theorem withdrawal_rows (tail : Nat → State) :
    pair_forest_trace.validate_forest_poseidon_rows (banks true tail) = ok (.Ok ()) :=
  PV_RunJoin_BankAggregate18.rows _ (withdrawal_blocks tail)
#print axioms withdrawal_rows
end R1Z.PV_RunJoin_FixtureBanks19
