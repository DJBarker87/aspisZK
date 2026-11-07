from NMT_formal import *
for n,m in [(52,'NMT_345Guard'),(53,'NMT_328Fold')]:
 r=run(f'NMT_L{n:03}','lean',m)
 # Independent members proceed even on a failure.
