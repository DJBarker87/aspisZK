#!/usr/bin/env python3
"""Independent message-inbox model. VerifiedSource is an explicit trust premise.

This module never interprets a mock boolean as cryptographic acceptance. Runtime
evidence supplies source transitions established by the pinned Pool/verifier.
All hashing/tree code here is independent of the Rust handler implementation.
"""
import copy
import hashlib
import random
import struct
import unittest
from dataclasses import dataclass, field, replace

DEPTH = 20
DOMAIN = b"aspis/research/v8/atomic-message/v1"
NODE = DOMAIN + b"/node"
EMPTY = hashlib.sha256(DOMAIN + b"/empty").digest()
RELEASE = hashlib.sha256(DOMAIN + b"/release:pool-asq8:sha256-depth20:message-only").digest()

def h(*parts):
    return hashlib.sha256(b"".join(parts)).digest()

def u64(n):
    return struct.pack("<Q", n)

def zeros(depth=DEPTH):
    result = [EMPTY]
    for _ in range(depth):
        result.append(h(NODE, result[-1], result[-1]))
    return result

def tree_root(leaves, depth=DEPTH):
    """Sparse level-by-level reconstruction, not a path-fold implementation."""
    z = zeros(depth)
    nodes = dict(enumerate(leaves))
    for level in range(depth):
        nodes = {i: h(NODE, nodes.get(2*i, z[level]), nodes.get(2*i+1, z[level]))
                 for i in {j//2 for j in nodes}}
    return nodes.get(0, z[depth])

def append_path(leaves, depth=DEPTH):
    z, nodes, index, result = zeros(depth), dict(enumerate(leaves)), len(leaves), []
    for level in range(depth):
        result.append(nodes.get(index ^ 1, z[level]))
        nodes = {i: h(NODE, nodes.get(2*i, z[level]), nodes.get(2*i+1, z[level]))
                 for i in {j//2 for j in nodes}}
        index //= 2
    return result

@dataclass(frozen=True)
class VerifiedSource:
    program: bytes
    verifier: bytes
    master: bytes
    lane: bytes
    proof_account: bytes
    old_sequence: int
    old_root: bytes
    new_root: bytes
    request: bytes             # exact canonical 320-byte ASQ8
    nullifier: bytes
    asset: int

def receipt(source, destination_program, inbox, sequence, root):
    return h(DOMAIN, RELEASE, destination_program, source.program, source.verifier,
             source.master, source.lane, source.proof_account,
             u64(source.old_sequence), source.old_root,
             u64(source.old_sequence+1), source.new_root,
             inbox, u64(sequence), root, source.request)

@dataclass
class State:
    a_root: bytes
    a_sequence: int
    source_master: bytes
    asset: int
    destination_program: bytes
    inbox: bytes
    leaves: list = field(default_factory=list)
    consumed: set = field(default_factory=set)  # (source master, nullifier), NEVER destination

def transition(state, source, expected_b_root, expected_b_sequence, expected_new_root,
               supplied_receipt, path, *, fail_after_source=False, fail_after_b=False):
    """Pure all-or-nothing transition, assuming authenticated VerifiedSource.

    No source verifier soundness theorem or Solana rollback theorem is asserted.
    No amounts or assets are credited to B. The receipt is data only.
    """
    if source.master != state.source_master or source.asset != state.asset:
        raise ValueError("route")
    if source.lane == state.inbox or source.program == state.destination_program:
        raise ValueError("roles")
    if (source.old_root, source.old_sequence) != (state.a_root, state.a_sequence):
        raise ValueError("stale A")
    if (source.master, source.nullifier) in state.consumed:
        raise ValueError("spent globally in A")
    n = len(state.leaves)
    if n >= 1 << DEPTH or (expected_b_sequence, expected_b_root) != (n, tree_root(state.leaves)):
        raise ValueError("stale/full B")
    updated = copy.deepcopy(state)
    updated.a_root, updated.a_sequence = source.new_root, source.old_sequence + 1
    updated.consumed.add((source.master, source.nullifier))
    if fail_after_source:
        raise ValueError("after source")
    leaf = receipt(source, state.destination_program, state.inbox, n, expected_b_root)
    if leaf != supplied_receipt or path != append_path(state.leaves):
        raise ValueError("receipt/path")
    updated.leaves.append(leaf)
    if tree_root(updated.leaves) != expected_new_root:
        raise ValueError("next B")
    if fail_after_b:
        raise ValueError("later instruction")
    return updated

class ModelTests(unittest.TestCase):
    def test_random_sequences_and_failures(self):
        rng = random.Random(0xA208)
        def digest(): return rng.randbytes(32)
        for trial in range(8):
            state = State(digest(), 13 if trial%2 else 255, digest(), 7, digest(), digest())
            for i in range(40):
                source = VerifiedSource(digest(), digest(), state.source_master, digest(),
                    digest(), state.a_sequence, state.a_root, digest(), rng.randbytes(320), digest(), 7)
                root, n = tree_root(state.leaves), len(state.leaves)
                leaf = receipt(source, state.destination_program, state.inbox, n, root)
                nxt = tree_root(state.leaves + [leaf])
                args = (source, root, n, nxt, leaf, append_path(state.leaves))
                before = copy.deepcopy(state)
                for flag in ["fail_after_source", "fail_after_b"]:
                    with self.assertRaises(ValueError): transition(state, *args, **{flag:True})
                    self.assertEqual(state, before)
                for pos in [1, 2, 3, 4, 5]:
                    bad = list(args)
                    bad[pos] = ([digest()] * DEPTH if pos == 5 else n+1 if pos == 2 else digest())
                    with self.assertRaises(ValueError): transition(state, *bad)
                state = transition(state, *args)
                self.assertEqual(state.a_sequence, before.a_sequence+1)
                self.assertEqual(len(state.leaves), n+1)
                self.assertEqual(len(state.consumed), n+1)
                with self.assertRaises(ValueError): transition(state, *args)
                routed = replace(state, inbox=digest(), a_root=source.old_root, a_sequence=source.old_sequence)
                with self.assertRaises(ValueError): transition(routed, *args)

    def test_receipt_binds_each_context_byte(self):
        s = VerifiedSource(*[bytes([j])*32 for j in range(1,6)], 13, b'a'*32,
                           b'b'*32, bytes(320), b'n'*32, 7)
        args = [s, b'd'*32, b'i'*32, 0, zeros()[-1]]
        expected = receipt(*args)
        # Nullifier/asset/recipient are canonical fields inside ASQ8, not duplicate scalars.
        for j in range(320):
            data = bytearray(s.request); data[j] ^= 1
            self.assertNotEqual(expected, receipt(replace(s, request=bytes(data)), *args[1:]))
        for field_name in ["program","verifier","master","lane","proof_account","old_root","new_root"]:
            self.assertNotEqual(expected, receipt(replace(s, **{field_name:b'x'*32}), *args[1:]))
        self.assertNotEqual(expected, receipt(replace(s,old_sequence=14), *args[1:]))
        for i in range(1,5):
            bad = args.copy(); bad[i] = 1 if i == 3 else b'z'*32
            self.assertNotEqual(expected, receipt(*bad))

if __name__ == "__main__":
    unittest.main(verbosity=2)
