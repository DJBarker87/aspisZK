"""Reference arithmetic for the wide-field screen: M31, CM31, QM31 and the two
candidate challenge fields.  Pure integers; used to generate fixtures and to
check the SBF kernels' outputs.

  CM31 = M31[i]/(i^2+1)            element (a, b)
  QM31 = CM31[u]/(u^2-(2+i))       element (c0, c1), as in aspis-core
  K8   = QM31[v]/(v^2-u)           element (x0, x1), degree 8 over M31
  K6   = CM31[w]/(w^3-XI)          element (y0, y1, y2), degree 6 over M31
"""
P = 2**31 - 1

def cadd(x, y): return ((x[0]+y[0]) % P, (x[1]+y[1]) % P)
def csub(x, y): return ((x[0]-y[0]) % P, (x[1]-y[1]) % P)
def cmul(x, y): return ((x[0]*y[0]-x[1]*y[1]) % P, (x[0]*y[1]+x[1]*y[0]) % P)
def cscale(x, s): return (x[0]*s % P, x[1]*s % P)
C0, C1 = (0, 0), (1, 0)
R = (2, 1)                                   # u^2 = 2 + i
def cpow(x, e):
    r = C1
    while e:
        if e & 1: r = cmul(r, x)
        x = cmul(x, x); e >>= 1
    return r
def cinv(x): return cpow(x, P*P-2)

def qadd(x, y): return (cadd(x[0], y[0]), cadd(x[1], y[1]))
def qsub(x, y): return (csub(x[0], y[0]), csub(x[1], y[1]))
def qmul(x, y):
    return (cadd(cmul(x[0], y[0]), cmul(R, cmul(x[1], y[1]))),
            cadd(cmul(x[0], y[1]), cmul(x[1], y[0])))
def qscale(x, s): return (cscale(x[0], s), cscale(x[1], s))
Q0, Q1 = (C0, C0), (C1, C0)
U = (C0, C1)
def qpow(x, e):
    r = Q1
    while e:
        if e & 1: r = qmul(r, x)
        x = qmul(x, x); e >>= 1
    return r
def qinv(x): return qpow(x, P**4-2)

# K8
def omul(x, y):
    return (qadd(qmul(x[0], y[0]), qmul(U, qmul(x[1], y[1]))),
            qadd(qmul(x[0], y[1]), qmul(x[1], y[0])))
def oscale(x, s): return (qscale(x[0], s), qscale(x[1], s))
def oinv(x):
    norm = qsub(qmul(x[0], x[0]), qmul(U, qmul(x[1], x[1])))
    n = qinv(norm)
    return (qmul(x[0], n), qmul(qsub(Q0, x[1]), n))
O1 = (Q1, Q0)

# K6
XI = (2, 1)                                  # checked below to be a non-cube
def hmul(x, y):
    a0, a1, a2 = x; b0, b1, b2 = y
    c0 = cadd(cmul(a0, b0), cmul(XI, cadd(cmul(a1, b2), cmul(a2, b1))))
    c1 = cadd(cadd(cmul(a0, b1), cmul(a1, b0)), cmul(XI, cmul(a2, b2)))
    c2 = cadd(cadd(cmul(a0, b2), cmul(a2, b0)), cmul(a1, b1))
    return (c0, c1, c2)
def hscale(x, s): return tuple(cscale(c, s) for c in x)
H1 = (C1, C0, C0)

def check_fields():
    # u is a non-square in QM31, so v^2 - u is irreducible and K8 is a field.
    assert qpow(U, (P**4-1)//2) == qsub(Q0, Q1)
    # XI is a non-cube in CM31 (3 divides p^2-1), so w^3 - XI is irreducible.
    assert (P*P-1) % 3 == 0 and cpow(XI, (P*P-1)//3) != C1
    # spot checks of the inverse formulas
    x = (((3, 5), (7, 11)), ((13, 17), (19, 23)))
    assert omul(x, oinv(x)) == O1
    assert qmul(x[0], qinv(x[0])) == Q1

if __name__ == "__main__":
    check_fields(); print("field checks ok: u non-square in QM31; 2+i non-cube in CM31")
