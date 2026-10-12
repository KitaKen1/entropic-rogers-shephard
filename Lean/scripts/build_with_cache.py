"""Compile local modules against a read-only, already built Mathlib checkout.

For a normal portable build use `lake update`, `lake exe cache get`, `lake build`.
This alternative avoids rebuilding or modifying a shared Mathlib cache.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument('--mathlib', type=Path, required=True)
parser.add_argument('--lean', default='lean')
parser.add_argument('--threads', type=int, default=1)
parser.add_argument('--incremental', action='store_true')
parser.add_argument('modules', nargs='*')
args = parser.parse_args()
mathlib = args.mathlib.resolve()
expected_mathlib = re.search(r'rev = "([0-9a-f]+)"', (ROOT / 'lakefile.toml').read_text()).group(1)
actual_mathlib = subprocess.check_output(['git', '-C', str(mathlib), 'rev-parse', 'HEAD'], text=True).strip()
if actual_mathlib != expected_mathlib:
    raise SystemExit(f'Mathlib commit mismatch: expected {expected_mathlib}, found {actual_mathlib}')
expected_lean = (ROOT / 'lean-toolchain').read_text().strip().split(':v')[-1]
lean_version = subprocess.check_output([args.lean, '--version'], text=True).strip()
if f'version {expected_lean},' not in lean_version:
    raise SystemExit(f'Lean toolchain mismatch: expected {expected_lean}, found {lean_version}')
build = ROOT / '.lake/build/lib/lean'
build.mkdir(parents=True, exist_ok=True)
paths = [build, mathlib / '.lake/build/lib/lean']
manifest = json.loads((mathlib / 'lake-manifest.json').read_text())
for package in manifest['packages']:
    candidates = [mathlib.parent / package['name'], mathlib / '.lake/packages' / package['name']]
    found = next((p / '.lake/build/lib/lean' for p in candidates
                  if (p / '.lake/build/lib/lean').is_dir()), None)
    if found is not None:
        paths.append(found)
env = os.environ.copy()
env['LEAN_PATH'] = os.pathsep.join(map(str, paths))
sources = {str(p.relative_to(ROOT).with_suffix('')).replace('/', '.'): p
           for p in ROOT.rglob('*.lean') if '.lake' not in p.parts}
targets = args.modules or ['EntropicRogersShephard', 'EntropicRogersShephard.Audit']
ordered = []
seen = set()

def visit(module):
    if module in seen:
        return
    seen.add(module)
    source = sources.get(module)
    if source is None:
        if module.startswith(('EntropicRogersShephard', 'LeanPool')):
            raise SystemExit(f'Missing local module: {module}')
        return
    for imported in re.findall(r'^(?:public )?import ([\w.]+)', source.read_text(), re.M):
        visit(imported)
    ordered.append((module, source))

for target in targets:
    visit(target)
results = []
log_dir = ROOT / 'verification'
log_dir.mkdir(exist_ok=True)
for module, source in ordered:
    source_hash = hashlib.sha256(source.read_bytes()).hexdigest()
    output = build / source.relative_to(ROOT).with_suffix('.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    dependencies = [build / sources[m].relative_to(ROOT).with_suffix('.olean')
                    for m in re.findall(r'^(?:public )?import ([\w.]+)', source.read_text(), re.M)
                    if m in sources]
    if (args.incremental and output.exists() and output.stat().st_mtime > source.stat().st_mtime
            and all(p.exists() and output.stat().st_mtime >= p.stat().st_mtime for p in dependencies)):
        print(f'{module}: reuse previously compiled module', flush=True)
        results.append({'module': module, 'sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                        'status': 'reused'})
        continue
    command = [args.lean, f'-j{args.threads}', '-o', str(output), str(source.relative_to(ROOT))]
    started = time.monotonic()
    process = subprocess.run(command, cwd=ROOT, env=env, text=True,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    elapsed = round(time.monotonic() - started, 2)
    log = '\n'.join(line.rstrip() for line in process.stdout.splitlines())
    if log:
        log += '\n'
    if source_hash != hashlib.sha256(source.read_bytes()).hexdigest():
        output.unlink(missing_ok=True)
        raise SystemExit(f'Source changed during compilation; rebuild {module}')
    (log_dir / (module + '.log')).write_text(log)
    record = {'module': module, 'sha256': source_hash,
              'seconds': elapsed, 'exit_code': process.returncode}
    results.append(record)
    print(f'{module}: exit {process.returncode}, {elapsed}s', flush=True)
    if log:
        print(log, flush=True)
    if process.returncode:
        (log_dir / 'latest-build.json').write_text(json.dumps(results, indent=2) + '\n')
        raise SystemExit(process.returncode)
(log_dir / 'latest-build.json').write_text(json.dumps(results, indent=2) + '\n')
(log_dir / 'environment.json').write_text(json.dumps({
    'lean': lean_version, 'mathlib': actual_mathlib,
    'mathlib_rebuilt_from_source': False,
    'method': 'Lean compiler against an existing read-only Mathlib build cache',
}, indent=2) + '\n')
