#!/usr/bin/env python3
"""Independent SPEC §§3–5 oracle; stdlib only, no Rust calls/imports.

E arithmetic is sparse multivariate polynomial multiplication/reduction by
(i²+1,u²−2−i,v²−u), NOT the Rust tower/Karatsuba routines. Inversion uses
Fermat exponentiation. Natural polynomials use integer convolution modulo p;
monomial conversion uses leading-term subtraction, not stored inverse
matrix multiplication. --check compares the entire deterministic fixture.
"""
import argparse
import hashlib
from pathlib import Path

P = 2**31 - 1
ZERO = (0,) * 8
ONE = (1,) + (0,) * 7


def reduce_term(i, u, v, c=1):
    if v >= 2:
        return reduce_term(i, u + 1, v - 2, c)
    if u >= 2:
        a = reduce_term(i, u - 2, v, 2 * c)
        b = reduce_term(i + 1, u - 2, v, c)
        return [x + y for x, y in zip(a, b)]
    if i >= 2:
        return reduce_term(i - 2, u, v, -c)
    out = [0] * 8
    out[i + 2*u + 4*v] = c
    return out


PRODUCTS = [[reduce_term((a & 1) + (b & 1), ((a >> 1) & 1) + ((b >> 1) & 1),
                         (a >> 2) + (b >> 2)) for b in range(8)] for a in range(8)]
PRODUCTS = [[[(i, c) for i, c in enumerate(v) if c] for v in row] for row in PRODUCTS]


def add(a, b): return tuple((x+y) % P for x, y in zip(a, b))
def neg(a): return tuple(-x % P for x in a)
def sub(a, b): return add(a, neg(b))
def scale(a, n): return tuple(x*n % P for x in a)


def mul(a, b):
    out = [0] * 8
    for i, x in enumerate(a):
        if not x: continue
        for j, y in enumerate(b):
            if not y: continue
            xy = x*y
            for k, c in PRODUCTS[i][j]: out[k] += c*xy
    return tuple(x % P for x in out)


def power(a, n):
    out = ONE
    while n:
        if n & 1: out = mul(out, a)
        a = mul(a, a)
        n >>= 1
    return out


def inv(a):
    assert a != ZERO
    return power(a, P**8-2)


def embed(x): return (x % P,) + (0,) * 7

def poly_mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): out[i+j] = (out[i+j] + x*y) % P
    return out


def natural_polynomials(n):
    factors = [[0, 1]]
    while 2**len(factors) < n:
        new = [(2*x) % P for x in poly_mul(factors[-1], factors[-1])]
        new[0] = (new[0] - 1) % P
        factors.append(new)
    columns = []
    for j in range(n):
        poly = [1]
        for b, factor in enumerate(factors):
            if (j >> b) & 1: poly = poly_mul(poly, factor)
        columns.append(poly + [0]*(n-len(poly)))
    return columns


def to_natural(poly, columns):
    n = len(columns)
    remainder = list(poly[:n]) + [ZERO] * max(0, n-len(poly))
    out = [ZERO]*n
    for j in reversed(range(n)):
        c = scale(remainder[j], pow(columns[j][j], P-2, P))
        out[j] = c
        if c != ZERO:
            for d in range(j+1):
                if columns[j][d]: remainder[d] = sub(remainder[d], scale(c, columns[j][d]))
    assert all(v == ZERO for v in remainder)
    return out


def to_monomial(coefficients, columns):
    out = [ZERO] * len(columns)
    for c, column in zip(coefficients, columns):
        for d, scalar in enumerate(column):
            if scalar: out[d] = add(out[d], scale(c, scalar))
    return out


def message(seed):
    return [tuple(((j+1)*(h+2)*seed + j*j*(h+1) + 17*h + 11) % P
                  for h in range(8)) for j in range(1024)]


def poly_eval(p, x):
    out = ZERO
    for c in reversed(p): out = add(c, mul(x, out))
    return out


def pair_eval(pair, z): return add(poly_eval(pair[0], z[0]), mul(z[1], poly_eval(pair[1], z[0])))


def circle(t):
    t2 = mul(t, t)
    inverse = inv(add(ONE, t2))
    return mul(sub(ONE, t2), inverse), mul(scale(t, 2), inverse)


def base_circle_mul(a, b): return ((a[0]*b[0]-a[1]*b[1]) % P, (a[0]*b[1]+a[1]*b[0]) % P)

def base_circle_pow(n):
    out, a = (1, 0), (2, 1268011823)
    while n:
        if n & 1: out = base_circle_mul(out, a)
        a = base_circle_mul(a, a)
        n >>= 1
    return out


def stored(i):
    u, s = divmod(i, 4)
    r = int(f'{u:018b}'[::-1], 2)
    n = [2*r, 2**20-1-2*r, 2**19+2*r, 2**19-1-2*r][s]
    return tuple(embed(x) for x in base_circle_pow(1024*(2*n+1)))


def interpolation(z0, z1, ys):
    axis = 0 if z0[0] != z1[0] else 1
    slope = mul(sub(ys[1], ys[0]), inv(sub(z1[axis], z0[axis])))
    out = [ZERO]*1024
    out[0] = sub(ys[0], mul(slope, z0[axis]))
    out[2 if axis == 0 else 1] = slope
    return out


def secant(z0, z1): return sub(mul(z0[0], z1[1]), mul(z1[0], z0[1])), sub(z0[1], z1[1]), sub(z1[0], z0[0])


def chord_pair(a, b, c, p, r):
    # Full untruncated polynomial multiplication, THEN truncate at lift.
    h0, h1 = [ZERO]*514, [ZERO]*513
    for d in range(512):
        h0[d] = add(h0[d], add(mul(a, p[d]), mul(c, r[d])))
        h0[d+1] = add(h0[d+1], mul(b, p[d]))
        h0[d+2] = sub(h0[d+2], mul(c, r[d]))
        h1[d] = add(h1[d], add(mul(c, p[d]), mul(a, r[d])))
        h1[d+1] = add(h1[d+1], mul(b, r[d]))
    return h0, h1


def interleave(a, b): return [v for pair in zip(a, b) for v in pair]

def matrix_hash(columns):
    n = len(columns)
    return hashlib.sha256(b''.join(columns[j][d].to_bytes(4, 'little') for d in range(n) for j in range(n))).hexdigest()


def inverse_columns(columns):
    # Scalar leading-term subtraction, independent from Rust's row solve.
    n = len(columns)
    result = []
    diagonal = [pow(columns[j][j], P-2, P) for j in range(n)]
    for k in range(n):
        remainder = [0]*n
        remainder[k] = 1
        out = [0]*n
        for j in reversed(range(k+1)):
            c = remainder[j]*diagonal[j] % P
            out[j] = c
            if c:
                for d in range(j+1): remainder[d] = (remainder[d]-c*columns[j][d]) % P
        assert not any(remainder)
        result.append(out)
    return result


def generate():
    lines = ['# Independent R-C KAT v1; values are eight canonical base-p limbs.']
    def emit(name, values):
        flat = [str(x) for value in values for x in value]
        lines.append(name + ' ' + ' '.join(flat))
    columns = natural_polynomials(512)
    final_columns = [col[:256] for col in columns[:256]]
    for n, m in [(256, final_columns), (512, columns)]:
        lines.append(f'matrix{n} {matrix_hash(m)}')
        lines.append(f'inverse{n} {matrix_hash(inverse_columns(m))}')
    q, w = message(19), message(37)
    pair = to_monomial(q[::2], columns), to_monomial(q[1::2], columns)
    z0 = circle((17,29,43,71,0,0,0,0))
    z1 = circle((101,103,107,109,0,0,0,0))
    emit('points', [*z0, *z1])
    a,b,c = secant(z0,z1)
    emit('secant', [a,b,c])
    indices = [0,1,2,3,4,5,6,7,492,493,494,495,524287,524288,1048572,1048573,1048574,1048575]
    lines.append('indices ' + ' '.join(map(str, indices)))
    emit('domain', [coordinate for i in indices for coordinate in stored(i)])
    emit('initial', [pair_eval(pair, stored(i)) for i in indices])
    emit('ood', [pair_eval(pair, z0), pair_eval(pair, z1)])
    alpha = (2,3,5,7,11,13,17,19)
    powers = [power(alpha, j) for j in range(4)]
    def dot(a,b):
        out = ZERO
        for x,y in zip(a,b): out=add(out,mul(x,y))
        return out
    folded = [dot(q[4*d:4*d+4], powers) for d in range(256)]
    dual = [dot(w[4*d:4*d+4], [powers[j] for j in [0,3,2,1]]) for d in range(256)]
    emit('fold_message', folded)
    emit('dual_fold', dual)
    fibres = [0,1,123,131071,131072,262143]
    lines.append('fibres ' + ' '.join(map(str, fibres)))
    final = to_monomial(folded, final_columns)
    emit('final', [poly_eval(final, sub(scale(mul(stored(4*u)[0],stored(4*u)[0]),2),ONE)) for u in fibres])
    # Arbitrary values, not just a codeword, check channel signs and divisions.
    values = q[:4]
    x,y = stored(492)
    quarter = embed(pow(4,P-2,P))
    phi = [dot(values, list(map(embed, signs))) for signs in
           [(1,1,1,1),(1,-1,-1,1),(1,1,-1,-1),(1,-1,1,-1)]]
    phi = [mul(v, mul(quarter, inv(d))) for v,d in zip(phi,[ONE,y,x,mul(x,y)])]
    emit('phi',phi)
    emit('fold_fibre',[dot(phi,powers)])
    ys = [q[0],q[1]]
    emit('interpolant_x',interpolation(z0,z1,ys)[:3])
    emit('interpolant_y',interpolation(z0,(z0[0],neg(z0[1])),ys)[:3])
    h0,h1 = chord_pair(a,b,c,*pair)
    emit('chord_message',interleave(to_natural(h0,columns),to_natural(h1,columns)))
    emit('functionals',[pair[1][511],sub(mul(b,pair[0][511]),mul(c,pair[1][510]))])
    # Entire transpose row: each column is multiplication of one N_j. Build
    # X*N_j and X²*N_j by scalar leading-term subtraction, then dot w.
    # This does not use the Rust M^T A^T M^(-T) factorization.
    diagonal = [pow(columns[j][j],P-2,P) for j in range(512)]
    def convert_scalar(poly):
        rem = list(poly[:512])
        out = [0]*512
        for j in reversed(range(512)):
            cc=rem[j]*diagonal[j]%P
            out[j]=cc
            if cc:
                for d in range(j+1): rem[d]=(rem[d]-cc*columns[j][d])%P
        return out
    def scalar_dot(coeffs, ws):
        out=ZERO
        for cc,ww in zip(coeffs,ws):
            if cc: out=add(out,scale(ww,cc))
        return out
    weights=[]
    for j in range(512):
        xn=convert_scalar([0]+columns[j])
        xxn=convert_scalar([0,0]+columns[j])
        even=add(add(mul(a,w[2*j]),mul(b,scalar_dot(xn,w[::2]))),mul(c,w[2*j+1]))
        odd=add(mul(c,sub(w[2*j],scalar_dot(xxn,w[::2]))),
                add(mul(a,w[2*j+1]),mul(b,scalar_dot(xn,w[1::2]))))
        weights.extend([even,odd])
    emit('quotient_weights',weights)
    return '\n'.join(lines)+'\n'


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    path=Path(__file__).with_name('kats.txt')
    output=generate()
    if args.check:
        if not path.exists() or path.read_text()!=output: raise SystemExit('KAT mismatch')
        print('KATs match independent oracle')
    else:
        path.write_text(output)
        print(f'wrote {path.name} ({len(output)} bytes)')
