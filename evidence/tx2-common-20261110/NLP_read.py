from pathlib import Path
import lzma
def read_text(p):
 p=Path(p)
 return p.read_text() if p.exists() else lzma.decompress(Path(str(p)+".xz").read_bytes()).decode()
