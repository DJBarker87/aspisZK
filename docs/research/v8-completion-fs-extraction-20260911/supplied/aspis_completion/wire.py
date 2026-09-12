"""Pinned selected-q22 wire projection; no cryptographic acceptance claim.

Layout cross-checked against SelectedWireBytes/PackedQueryRecord at 30a303a.
This parser deliberately binds each projection to ONE immutable body. A local
repaired profile must be reconciled before using it as an implementation oracle.
"""
from __future__ import annotations
from dataclasses import dataclass
from hashlib import sha256
from struct import unpack_from
from typing import Sequence

P = (1 << 31) - 1
FIXED_FIELDS = 697
FIXED_BYTES = FIXED_FIELDS * 16
C1_ROOT_OFFSET = 11152
C2_ROOT_OFFSET = 11178
NONCE_OFFSET = 11204
RECORD_OFFSET = 11228
RECORD_BYTES = 621
QUERY_COUNT = 22
FRONTIER_OFFSET = 24890
FRONTIER_CAP = 296
MAX_BODY_BYTES = 40282

class WireError(ValueError):
    pass

def canonical_u32_le(data: bytes, offset: int = 0) -> int:
    if offset < 0 or offset + 4 > len(data):
        raise WireError("truncated M31 limb")
    value = unpack_from('<I', data, offset)[0]
    if value >= P:
        raise WireError("noncanonical M31 limb")
    return value

def unpack31(data: bytes, count: int) -> tuple[int, ...]:
    if count < 0 or count * 31 != len(data) * 8:
        raise WireError("expected exact byte-aligned packed31 record")
    aggregate = int.from_bytes(data, 'little')
    result = tuple((aggregate >> (31 * i)) & P for i in range(count))
    if any(x >= P for x in result):
        raise WireError("packed all-ones limb is not canonical")
    return result

def pack31(values: Sequence[int]) -> bytes:
    if len(values) * 31 % 8:
        raise WireError("packed input does not end on a byte boundary")
    if any(type(x) is not int or x < 0 or x >= P for x in values):
        raise WireError("noncanonical packed input")
    aggregate = sum(x << (31 * i) for i, x in enumerate(values))
    return aggregate.to_bytes(len(values) * 31 // 8, 'little')

@dataclass(frozen=True)
class PackedRecord:
    raw: bytes
    c1_limbs: tuple[int, ...]
    c2_limbs: tuple[int, ...]
    salt: bytes

    def __post_init__(self):
        if not isinstance(self.raw, bytes) or len(self.raw) != RECORD_BYTES:
            raise WireError('immutable exact raw record required')
        if self.c1_limbs != unpack31(self.raw[:403],104) or self.c2_limbs != unpack31(self.raw[403:589],48) or self.salt != self.raw[589:]:
            raise WireError('decoded record does not match its raw bytes')

    @classmethod
    def parse(cls, raw: bytes) -> 'PackedRecord':
        raw = bytes(raw)
        if len(raw) != RECORD_BYTES:
            raise WireError("record must be exactly 621 bytes")
        return cls(raw, unpack31(raw[:403], 104), unpack31(raw[403:589], 48), raw[589:])

    def c1(self, slot: int, column: int) -> int:
        if not 0 <= slot < 4 or not 0 <= column < 26:
            raise IndexError('C1 coordinate')
        # Candidate slot-major index adapter; bind c1LimbIndex from the repaired source before certification.
        return self.c1_limbs[slot * 26 + column]

    def c2(self, helper: int, slot: int) -> tuple[int, int, int, int]:
        if not 0 <= helper < 3 or not 0 <= slot < 4:
            raise IndexError('C2 coordinate')
        start = (helper * 4 + slot) * 4
        return self.c2_limbs[start:start + 4]

@dataclass(frozen=True)
class Wire:
    body: bytes

    def __post_init__(self):
        object.__setattr__(self, 'body', bytes(self.body))
        extra = len(self.body) - FRONTIER_OFFSET
        if extra < 0 or extra % 52 or extra // 52 > FRONTIER_CAP:
            raise WireError("length is not 24890 + 52*c for 0<=c<=296")
        for i in range(FIXED_FIELDS * 4):
            canonical_u32_le(self.body, 4*i)

    @classmethod
    def parse(cls, body: bytes, *, decode_records: bool = False) -> 'Wire':
        wire = cls(bytes(body))
        if decode_records:
            for record in wire.records:
                PackedRecord.parse(record)
        return wire

    @property
    def fields(self) -> tuple[tuple[int, int, int, int], ...]:
        return tuple(tuple(canonical_u32_le(self.body,16*i+4*j) for j in range(4))
                     for i in range(FIXED_FIELDS))

    @property
    def roots(self) -> tuple[bytes,bytes]:
        return self.body[11152:11178], self.body[11178:11204]

    @property
    def nonces(self) -> tuple[bytes,bytes,bytes]:
        return tuple(self.body[11204+8*i:11212+8*i] for i in range(3))

    @property
    def records(self) -> tuple[bytes,...]:
        return tuple(self.body[11228+621*i:11228+621*(i+1)] for i in range(22))

    @property
    def frontiers(self) -> tuple[tuple[bytes,...],tuple[bytes,...]]:
        count=(len(self.body)-24890)//52;half=26*count
        return tuple(tuple(self.body[24890+phase*half+26*i:24890+phase*half+26*(i+1)]
                           for i in range(count)) for phase in range(2))

    @property
    def digest(self) -> str:
        # An evidence identifier, not the protocol transcript digest.
        return sha256(self.body).hexdigest()

    def assert_same_body(self, other: 'Wire') -> None:
        if self.body != other.body:
            raise WireError('different bodies; hash/root equality is not sufficient')

    def semantic_field(self, index: int) -> tuple[int, int, int, int]:
        if not 0 <= index < FIXED_FIELDS:
            raise IndexError('fixed field')
        return tuple(canonical_u32_le(self.body,16*index+4*j) for j in range(4))


def synthetic_body(frontier_count: int = 0) -> bytes:
    """Parser fixture only. No claim that it is a valid Aspis proof."""
    if not 0 <= frontier_count <= FRONTIER_CAP:
        raise WireError('frontier count out of range')
    return bytes(FRONTIER_OFFSET + 52 * frontier_count)
