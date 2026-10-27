import ARX_Root
import Rc10_Top
-- Read-only audit of the existing roots: no theorem alias or proof is added.
set_option pp.all false
set_option pp.deepTerms true
set_option pp.fullNames true
set_option pp.explicit false
set_option pp.universes false
set_option pp.proofs false
set_option format.width 140
#check @AspisR1.Rc10_Top.deployed
#check @AspisR1.ARX_Root.deployed
#print AspisR1.ARX_Root.deployed
#print axioms AspisR1.Rc10_Top.deployed
#print axioms AspisR1.ARX_Root.deployed
