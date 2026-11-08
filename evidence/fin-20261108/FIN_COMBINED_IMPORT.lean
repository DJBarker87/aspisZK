import FIN_213
import FIN_330
/- Focused combined import of the five FIN_ roots, with the two
same-function identities (221 = 333 process, 213 = 330 entry). -/
set_option autoImplicit false
noncomputable section
namespace FIN_Combined

theorem process_same : @FIN_333.producer = @FIN_221.producer := rfl
theorem entry_same : @FIN_330.producer = @FIN_213.producer := rfl

#print axioms FIN_240.candidate
#print axioms FIN_221.candidate
#print axioms FIN_213.candidate
#print axioms FIN_333.candidate
#print axioms FIN_330.candidate
#print axioms process_same
#print axioms entry_same
end FIN_Combined
end
