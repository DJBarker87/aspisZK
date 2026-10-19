# Costs on the actual CompPoly factor/recovery path

CompPolyFactorTotalDivisionCost instruments the actual early-aborting factor recursion, preserving its output and left-before-right execution order. The total charged right-child division cost is at most (degree - 1) times a node-local bound. CompPolyFactorRawDivisionBridge connects the actual CPolynomial.divByMonic quotient to the already costed raw division and derives a polynomial bound on these actual division charges.

ActualCompPolyModPowerStepCount follows the actual Nat.binaryRec implementation of CompPolyPolynomialBackendBridge.modPower, rather than the different Raw.powModWith routine. Its value projection equals that implementation. It charges two high-level polynomial multiplications and one modByMonic operation per nonbase binary digit, bounded by 3*(log2(exponent)+1). ActualCompPolyEuclideanFuelBound identifies the maintained gcdMonic and division implementations with their exact fuel-bounded recursion: input-size sum plus one for GCD and dividend size for auxiliary division. These are recursion budgets, not full operation costs.

These charges do not yet include internal multiplication, remainder, GCD, normalization, field/bit arithmetic or array-allocation costs. This is progress toward the executable extractor's polynomial-time bound, not a complete cost theorem.

All four focused Lean 4.32 checks exited 0, with standard axioms only and zero process swaps. Exact metrics, source revision, commands, source/object/import hashes and full axiom output are in the receipts. Compiled objects are included. The retained original worker packet includes failed attempts and their replacement sources. These are working component checks, not a clean unified-manifest release or complete 100-bit theorem.
