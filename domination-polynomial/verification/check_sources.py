"""Check the recorded Lean source bytes; compile separately with Lake."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parent.parent
manifest = json.loads((root / 'verification' / 'source_manifest.json').read_text())
bad = [name for name, digest in manifest.items()
       if not (root / name).is_file()
       or hashlib.sha256((root / name).read_bytes()).hexdigest() != digest]
if bad:
    raise SystemExit('Source mismatch: ' + ', '.join(bad))
print(f'All {len(manifest)} recorded source hashes match.')
