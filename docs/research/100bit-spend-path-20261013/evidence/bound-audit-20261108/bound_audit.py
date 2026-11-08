# Exact-rational audit of AspisR1.F3T_Numeric.total and F3U_RangeEdges.maxQueries.
# All checks use fractions.Fraction / int. Decimal is used only to print logarithms.
from fractions import Fraction as F
from math import isqrt
from decimal import Decimal, getcontext
getcontext().prec = 60
P = lambda k: F(2) ** k
B = F(15) / P(109)                                   # PerAttemptEnvelope.B
start     = lambda Q: (Q + 34) * B                   # F3T_Probability.restricted_union_bound
collision = lambda Q: 6 * F(Q + 1161) ** 2 / P(256)  # BinCombinedMerkleCollision.kappa (Q+1161) = F3T_Numeric.collisionLoss
account   = lambda Q: 6 * F(Q + 2965) ** 2 / P(256)  # F3T_Numeric.accountLoss (E_rec, FJp_Mass.bounded)
abort     = F(1) / P(126)                            # RawRecordedOracleExtractionMassBin bankAbortMass envelope
scan      = F(1) / P(454)                            # QueryScanModelFailure.exhaustion_bound
def total(Q):           # F3T_Numeric.total
    return start(Q) + collision(Q) + account(Q) + abort + scan
def startcharge(Q):     # StartChargeNumeric.totalBound = envelope Q 34 1161
    return start(Q) + collision(Q) + abort + scan
target = lambda Q: F(Q + 1) / P(100)
def gap(x):             # F3U_RangePolynomial.gap, literal
    x = F(x)
    return 6 * ((x + 1161) ** 2 + (x + 2965) ** 2) / P(256) + (x + 34) * 15 / P(109) + 1 / P(126) + 1 / P(454) - (x + 1) / P(100)
def log2(fr):
    return (Decimal(fr.numerator).ln() - Decimal(fr.denominator).ln()) / Decimal(2).ln()

MAXQ_LEAN = 7388980242446479800895501321004157112314840375
out = []
def chk(name, cond):
    out.append(f"{'PASS' if cond else 'FAIL'}  {name}")
    assert cond, name

# 1. identities between Lean definitions
for Q in [0, 1, 2, 1000, 2**64, 2**100, MAXQ_LEAN, MAXQ_LEAN + 1, 2**160]:
    chk(f"total_gap  Q={Q}", total(Q) - target(Q) == gap(Q))
    chk(f"F3T_Combined.arithmetic Q={Q}", startcharge(Q) + account(Q) == total(Q))
# margin_exact
margin = 1 / P(108) - 6 * (F(1161) ** 2 + F(2965) ** 2) / P(256) - 1 / P(126) - 1 / P(454)
chk("margin_exact: 2^-100 - total(0) == F3U_Numeric.margin", target(0) - total(0) == margin)
chk("margin positive", margin > 0)
chk("34*B == 2^-100 - 2^-108", 34 * B == 1 / P(100) - 1 / P(108))

# 2. exact maxQueries from the quadratic (integer coefficients after scaling by 2^454)
S = P(454)
a2 = 12                                       # leading coeff of gap: 12/2^256
A = int(F(12) / P(256) * S)
Bq = int((F(12) * (1161 + 2965)) / P(256) * S + F(15) / P(109) * S - F(1) / P(100) * S)
C = int(gap(0) * S)
for Q in [0, 5, 10**40, MAXQ_LEAN]:
    chk(f"integer quadratic matches gap*2^454 at Q={Q}", A * Q * Q + Bq * Q + C == gap(Q) * S)
chk("gap(0) < 0 (so 0 lies between the roots)", C < 0)
disc = Bq * Bq - 4 * A * C
r = (-Bq + isqrt(disc)) // (2 * A)
while A * (r + 1) ** 2 + Bq * (r + 1) + C <= 0: r += 1
while A * r * r + Bq * r + C > 0: r -= 1
chk("largest integer Q with gap(Q) <= 0 equals F3U_RangeEdges.maxQueries", r == MAXQ_LEAN)
chk("total(maxQ) <= (maxQ+1)/2^100", total(MAXQ_LEAN) <= target(MAXQ_LEAN))
chk("total(maxQ+1) > (maxQ+2)/2^100", total(MAXQ_LEAN + 1) > target(MAXQ_LEAN + 1))
# convexity: A>0 and gap(0)<0 => {Q>=0 : gap(Q)<=0} = [0, maxQ]
chk("A > 0 (convex)", A > 0)

# 3. Option A comparison (second accountLoss)
def gapA(Q): return gap(Q) + account(Q)
AA = A + int(F(12) / P(256) * S) // 2   # 6/2^256 extra leading coefficient scaled
AA = int((F(12) + 6) / P(256) * S)
BA = int((F(12) * (1161 + 2965) + 12 * 2965) / P(256) * S + F(15) / P(109) * S - F(1) / P(100) * S)
CA = int(gapA(0) * S)
rA = (-BA + isqrt(BA * BA - 4 * AA * CA)) // (2 * AA)
while gapA(rA + 1) <= 0: rA += 1
while gapA(rA) > 0: rA -= 1
chk("option-A range equals EVB constant", rA == 4925986828297653200597000880669438074876558273)

# 4. Q = 0 figures
t0 = total(0)
out.append("")
out.append(f"total(0) exact = {t0}")
out.append(f"total(0) = {Decimal(t0.numerator)/Decimal(t0.denominator) * Decimal(2)**100} * 2^-100")
out.append(f"log2 total(0) = {log2(t0)}")
out.append(f"headroom bits  log2(2^-100/total(0)) = {log2(target(0)/t0)}")
out.append(f"margin = 2^-100 - total(0) = 2^{log2(margin)}")
out.append(f"margin / 2^-108 = {Decimal((margin*P(108)).numerator)/Decimal((margin*P(108)).denominator)}")
out.append(f"term shares at Q=0: start {Decimal((start(0)/t0).numerator)/Decimal((start(0)/t0).denominator)}, "
           f"collision {Decimal((collision(0)/t0).numerator)/Decimal((collision(0)/t0).denominator):.3E}, "
           f"account {Decimal((account(0)/t0).numerator)/Decimal((account(0)/t0).denominator):.3E}")
out.append(f"6*(1161^2+2965^2) = {6*(1161**2+2965**2)}")
out.append(f"log2 maxQueries = {log2(F(MAXQ_LEAN))}")
out.append(f"log2 option-A range = {log2(F(rA))}")
out.append(f"option-A / maxQ = {F(rA, MAXQ_LEAN)} (approx {Decimal(rA)/Decimal(MAXQ_LEAN)})")
out.append(f"log2 B = {log2(B)}")
# looseness factor of (Q+1)/2^100 vs total(Q) for large Q < 2^100
for Q in [0, 233, 10**6, 2**60, 2**99]:
    out.append(f"log2 ((Q+1)/2^100 / total(Q)) at Q={Q}: {log2(target(Q)/total(Q))}")
out.append(f"limit log2(2^9/15) = {log2(F(512,15))}")
# Q = 0 where account term is removed (margin for the pre-frozen3 envelope)
out.append(f"log2 (2^-100 - startcharge(0)) = {log2(target(0)-startcharge(0))}")
print("\n".join(out))
