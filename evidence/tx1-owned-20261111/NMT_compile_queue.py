from NMT_formal import *
for n,m in [(46,'NMT_RowSpec_094'),(47,'NMT_CallTree'),(48,'NMT_328Tree'),(49,'NMT_094Tree'),(50,'NMT_345Tree'),(51,'NMT_328Fold')]:
 r=run(f'NMT_L{n:03}','lean',m)
 if r['exit_status']:break
