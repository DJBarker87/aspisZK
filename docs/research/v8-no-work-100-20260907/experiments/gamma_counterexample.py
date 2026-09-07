"""Independent exact support/arithmetic check, not a non-interactive security certificate."""
from fractions import Fraction
from math import comb, log2
P=2**31-1
N=2**18
M=760
R=28
# Count pattern occurrences arithmetically, independent of the Rust fibre loop.
supports=[sum(N//M+int((g-j)%M<N%M) for j in range(R)) for g in range(M)]
assert min(supports)>9557 and sum(supports)==N*R
fixed_zero_max_bad_gammas=(R*N)//9558
gamma=Fraction(M,P**4-1)
query_lo=Fraction(comb(min(supports),22),comb(N,22))
query_hi=Fraction(comb(max(supports),22),comb(N,22))
print('support range:', min(supports), max(supports))
print('fixed-zero double-counting upper bound:', fixed_zero_max_bad_gammas)
print('exact gamma probability:',gamma)
print('gamma bits (display):',-log2(gamma))
print('uniform query-only bits (display interval):',-log2(query_hi),-log2(query_lo))
print('gamma-and-query event bits (display interval):',-log2(gamma*query_hi),-log2(gamma*query_lo))
print('No work credit, FS lifting, other checks, or final payment acceptance is included.')

# Symbol-level boundary case. Common zeros are one below the exact strict
# initial agreement threshold. Each remaining symbol gets 28 distinct roots.
SYMBOLS=2**20
COMMON=38229
symbol_bad=R*(SYMBOLS-COMMON)
assert symbol_bad<P  # all roots 1..symbol_bad are distinct legal M31 gammas
symbol_error=Fraction(symbol_bad,P**4-1)
assert symbol_error>Fraction(1,2**100)  # exact comparison, not a floating verdict
print('SYMBOL-LEVEL initial recovery counterexample:')
print('common zeros:',COMMON,'combined support per selected gamma:',COMMON+1)
print('distinct bad gammas:',symbol_bad,'exact isolated-stage error:',symbol_error)
print('isolated-stage bits (display):',-log2(symbol_error))
print('This does NOT establish the same lower bound for the joint fold/query/accepted-proof event.')
