# Exact integer arithmetic only; not an executed Rust/Lean field-reader proof.
word_bits=64
size=1<<word_bits
i=1<<(word_bits-5)
start=(i*32)%size
nxt=(i+1)%size
finish=(nxt*32)%size
assert i<size and start==0 and finish==32
assert i*32>=size
print('PASS arithmetic-only: wrapping [0,32), checked first multiply overflows; full-reader equality needs index bound.')
