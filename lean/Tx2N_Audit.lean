import Tx2N_Accepted
import Tx2N_Nonvacuity
import Port5Q2_ReaderSemantic
import Port5Q2_ReaderValidate
import Port5Q2_ReaderWeightJoin
import Port5Q2_ReaderScalar
set_option autoImplicit false
#print axioms AspisR1.Tx2N_Accepted.accepted_pair_reader
#print axioms AspisR1.Tx2N_Accepted.accepted_pair_inner
#print axioms AspisR1.Tx2N_Decode.actual
#print axioms AspisR1.Tx2N_DecodeHeader.range_to
#print axioms AspisR1.Tx2N_DecodeHeader.byte
#print axioms AspisR1.Tx2N_DecodeHeader.cast_value
#print axioms AspisR1.Tx2N_DecodeHeader.accepted
#print axioms AspisR1.Tx2N_Execution.common
#print axioms AspisR1.Tx2N_Fields.canonical_k
#print axioms AspisR1.Tx2N_Fields.canonical_e
#print axioms AspisR1.Tx2N_Fields.prepare
#print axioms AspisR1.Tx2N_Finish.accepted
#print axioms AspisR1.Tx2N_Header.guard
#print axioms AspisR1.Tx2N_Header.guard_prop
#print axioms AspisR1.Tx2N_Header.cuts
#print axioms AspisR1.Tx2N_Install.slots
#print axioms AspisR1.Tx2N_Install.retained
#print axioms AspisR1.Tx2N_Install.reader_success
#print axioms AspisR1.Tx2N_Nonvacuity.writer_equation
#print axioms AspisR1.Tx2N_Nonvacuity.powers_success
#print axioms AspisR1.Tx2N_Powers.roundtrip
#print axioms AspisR1.Tx2N_Powers.total_exact
#print axioms AspisR1.Tx2N_Query.release_ports
#print axioms AspisR1.Tx2N_Query.twelve
#print axioms AspisR1.Tx2N_Reader.writer_bytes
#print axioms AspisR1.Tx2N_Reader.saved_ten
#print axioms AspisR1.Tx2N_Reserved.loop_zeros
#print axioms AspisR1.Tx2N_Reserved.zeros
#print axioms AspisR1.Tx2N_Twelve.accepted
#print axioms AspisR1.Port4A_ReaderInstall.reference_eq
#print axioms AspisR1.Port5Q2_ReaderSemantic.normalization
#print axioms AspisR1.Port5Q2_ReaderValidate.reference
#print axioms AspisR1.Port5Q2_ReaderWeightJoin.accepted
#print axioms AspisR1.Port5Q2_ReaderScalar.current_k
#print axioms AspisR1.Port5Q2_ReaderScalar.current_e
#print AspisR1.Tx2N_Finish.Outcome
#print AspisR1.Tx2N_Install.inner
#print AspisR1.Tx2N_Execution.control
#check @AspisR1.Tx2N_Accepted.accepted_pair_inner
