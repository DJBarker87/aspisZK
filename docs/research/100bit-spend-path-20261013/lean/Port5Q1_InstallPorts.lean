import Port5Q1_QueryPorts
set_option autoImplicit false
namespace AspisR1.Port5Q1_InstallPorts
open AspisR1Stage2 Port3_NativeQueryBody Port5Q1_QueryPorts

theorem installed (ops : Ops) (ports : SessionAPrimitives ops) :
    SessionAPrimitives (install ops) :=
  ⟨⟨ports.basis.s3_s4_mul,ports.basis.s3_s4_sub,ports.basis.s3_s4_double,ports.basis.zero,ports.basis.one⟩,
   ⟨ports.arithmetic.s3_s4_s5_mulE,ports.arithmetic.s3_s4_s5_addE,ports.arithmetic.s3_s4_s9_mulK⟩,
   ⟨ports.m31.multiply,ports.m31.double,ports.m31.one,ports.m31.subtract⟩,
   ⟨ports.decoder.decode⟩,ports.line,ports.line_canonical⟩

theorem rows (ops : Ops) (ports : SessionAPrimitives ops) :
    SessionAPrimitives (Port4C_RowStd.install (install ops)) :=
  ⟨⟨ports.basis.s3_s4_mul,ports.basis.s3_s4_sub,ports.basis.s3_s4_double,ports.basis.zero,ports.basis.one⟩,
   ⟨ports.arithmetic.s3_s4_s5_mulE,ports.arithmetic.s3_s4_s5_addE,ports.arithmetic.s3_s4_s9_mulK⟩,
   ⟨ports.m31.multiply,ports.m31.double,ports.m31.one,ports.m31.subtract⟩,
   ⟨ports.decoder.decode⟩,ports.line,ports.line_canonical⟩

#print axioms installed
#print axioms rows
end AspisR1.Port5Q1_InstallPorts
