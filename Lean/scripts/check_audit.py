"""Check that every listed theorem has only the standard Lean logical axioms."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
source = ROOT / 'EntropicRogersShephard/Audit.lean'
log = ROOT / 'verification/EntropicRogersShephard.Audit.log'
expected = re.findall(r'^#print axioms ([\w.]+)', source.read_text(), re.M)
declared = {'brunn_minkowski'}
for proof_file in sorted(ROOT.glob('EntropicRogersShephard*.lean')) + sorted(
        (ROOT / 'EntropicRogersShephard').glob('*.lean')):
    if proof_file == source:
        continue
    declared.update('EntropicRogersShephard.' + name for name in re.findall(
        r'^(?:@\[[^\]]*\][ \t]*)?theorem (\w+)', proof_file.read_text(), re.M))
if set(expected) != declared or len(expected) != len(set(expected)):
    raise SystemExit(f'Audit source coverage mismatch: {declared ^ set(expected)}')
reported = dict(re.findall(r"'([\w.]+)' depends on axioms: \[([^\]]*)\]", log.read_text()))
for theorem in re.findall(r"'([\w.]+)' does not depend on any axioms", log.read_text()):
    reported[theorem] = ''
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
if set(reported) != set(expected):
    raise SystemExit(f'Axiom audit coverage mismatch: {set(expected) ^ set(reported)}')
for theorem, names in reported.items():
    axioms = {x.strip() for x in names.split(',') if x.strip()}
    if not axioms <= allowed:
        raise SystemExit(f'Unexpected axioms for {theorem}: {axioms - allowed}')
records = {}
for p in sorted(ROOT.rglob('*.lean')):
    if '.lake' not in p.parts:
        records[str(p.relative_to(ROOT))] = hashlib.sha256(p.read_bytes()).hexdigest()
result = {'audited_theorems': len(expected), 'allowed_axioms': sorted(allowed),
          'sorryAx': False, 'new_axioms': False, 'full_main_theorem_proved': False,
          'density_main_theorem_proved':
              'EntropicRogersShephard.sharp_entropic_rogers_shephard_density' in reported,
          'probability_law_connection_proved':
              'EntropicRogersShephard.sharp_entropic_rogers_shephard_random_vectors' in reported,
          'sharpness_proved':
              'EntropicRogersShephard.entropy_increment_constant_optimal' in reported,
          'constant_optimality_proved':
              'EntropicRogersShephard.entropy_increment_constant_optimal' in reported,
          'exponential_product_equality_proved':
              'EntropicRogersShephard.sharpness_exponential_product' in reported,
          'affine_image_equality_proved': False,
          'full_main_theorem_scope': 'Density inequality, probability-law connection, and sharpness for exponential products and invertible affine images.',
          'source_sha256': records}
(ROOT / 'verification/axiom-audit.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k != 'source_sha256'}, indent=2))
