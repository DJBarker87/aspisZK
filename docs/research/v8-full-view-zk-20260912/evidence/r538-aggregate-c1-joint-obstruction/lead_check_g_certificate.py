"""Independently check a saved QM31 left-kernel certificate, not source adequacy."""
import hashlib
import json
from pathlib import Path
import struct
import sys

P = 2147483647
ZERO = (0, 0, 0, 0)

def add(x, y):
    return tuple((a + b) % P for a, b in zip(x, y))

def cmul(x, y):
    a, b = x
    c, d = y
    return ((a*c - b*d) % P, (a*d + b*c) % P)

def mul(x, y):
    ac = cmul(x[:2], y[:2])
    bd = cmul(x[2:], y[2:])
    ad = cmul(x[:2], y[2:])
    bc = cmul(x[2:], y[:2])
    return ((ac[0] + 2*bd[0] - bd[1]) % P,
            (ac[1] + bd[0] + 2*bd[1]) % P,
            (ad[0] + bc[0]) % P, (ad[1] + bc[1]) % P)

def main(path):
    data = path.read_bytes()
    magic = b"R117GLEFTKERNEL1\0"
    assert data.startswith(magic)
    rows, cols = struct.unpack_from('<II', data, len(magic))
    start = len(magic) + 8
    assert len(data) == start + 16*(rows*cols + 2*rows)
    assert (rows, cols) == (626, 1022)
    vals = list(struct.iter_unpack('<4I', data[start:]))
    assert all(0 <= v < P for x in vals for v in x)
    matrix = vals[:rows*cols]
    rhs = vals[rows*cols:rows*cols+rows]
    coeff = vals[rows*cols+rows:]
    support = [(i, c) for i, c in enumerate(coeff) if c != ZERO]
    for col in range(cols):
        total = ZERO
        for row, c in support:
            total = add(total, mul(c, matrix[row*cols + col]))
        assert total == ZERO, (col, total)
    total_rhs = ZERO
    for row, c in support:
        total_rhs = add(total_rhs, mul(c, rhs[row]))
    assert total_rhs != ZERO
    print(json.dumps({
        'certificate_sha256': hashlib.sha256(data).hexdigest(),
        'matrix_shape': [rows, cols],
        'all_limbs_canonical': True,
        'all_original_columns_annihilated': True,
        'nonzero_coefficients': support,
        'supported_original_rhs': [(i, rhs[i]) for i, _ in support],
        'certificate_rhs': total_rhs,
        'boundary': 'Finite supplied matrix incompatibility only; no source or full-view privacy conclusion.'
    }, indent=2))

if __name__ == '__main__':
    main(Path(sys.argv[1]))
