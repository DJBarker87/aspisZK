from pathlib import Path
import subprocess
p=Path(__file__).with_name('run-rust.py')
for n in range(22):
 subprocess.run(['python3',str(p),f'contains-fixed{n}-v1',f'contains_len_{n}','30'],check=True)
