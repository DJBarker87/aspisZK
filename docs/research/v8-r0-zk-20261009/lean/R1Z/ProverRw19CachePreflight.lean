import R1Z.ProverRw18ArithmeticBounds
import R1Z.ProverRw19P6RawContextIdentity
set_option autoImplicit false
-- Host import/axioms check of an authenticated retained proof object against
-- the freshly checked generic context modules. This does not reprove a row.
#check R1Z.ProverRw18ArithmeticBounds.product_bound
#print axioms R1Z.ProverRw18ArithmeticBounds.product_bound
#print axioms R1Z.ProverRw19P6RawContextIdentity.identity
