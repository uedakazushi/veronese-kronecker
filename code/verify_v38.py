#!/usr/bin/env python3
"""Read-only execution of the five new v38 mathematical gates.

Complete JSON stdout must equal the committed certificate. Scripts, certificates
and scientific inputs are never regenerated. Only logs and reports beneath
verification/ are written. Historical inputs and reports remain untouched.
SymPy 1.14.0 and python-flint 0.9.0 are required; see requirements_v38.txt.
"""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import argparse
import hashlib
import importlib.metadata
import json
import os
import subprocess
import sys
import time


GATES = [{'name': 'endpoint_birational', 'script': 'verify_endpoint_birational_v38.py', 'certificate': 'endpoint_birational_v38_certificate.json', 'args': [], 'generation': 'new_v38'}, {'name': 'root_unity', 'script': 'verify_endpoint_root_unity_v38.py', 'certificate': 'endpoint_root_unity_v38_certificate.json', 'args': [], 'generation': 'new_v38'}, {'name': 'endpoint_mckay', 'script': 'verify_endpoint_mckay_v38.py', 'certificate': 'endpoint_mckay_v38_certificate.json', 'args': [], 'generation': 'new_v38'}, {'name': 'vk_symmetry_families', 'script': 'verify_vk_symmetry_families_v38.py', 'certificate': 'vk_symmetry_families_v38_certificate.json', 'args': ['--dump'], 'generation': 'new_v38'}, {'name': 'vk_completion_symmetry', 'script': 'verify_vk_completion_symmetry_v38.py', 'certificate': 'vk_completion_symmetry_v38_certificate.json', 'args': ['--dump'], 'generation': 'new_v38'}]


def digest(path):
    result = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024*1024), b''):
            result.update(block)
    return result.hexdigest()


def snapshot(root):
    """Protect code trees, all Python source, certificates and scientific inputs.

    This extends the v32 scope to independent audit scripts/certificates that
    live outside directories literally named `code`. The runner's new reports
    are not certificates and are excluded from this immutable scope.
    """
    paths = []
    for path in root.rglob('*'):
        if not path.is_file() or '__pycache__' in path.parts or path.suffix in ('.pyc', '.pyo'):
            continue
        rel = path.relative_to(root)
        is_protected = (
            'code' in rel.parts
            or path.suffix == '.py'
            or 'input' in rel.parts or 'inputs' in rel.parts
            or ('certificate' in path.name and path.suffix == '.json')
            or rel.as_posix().startswith('archive/extension_20261029/')
        )
        if is_protected:
            paths.append(path)
    return {p.relative_to(root).as_posix(): digest(p)
            for p in sorted(paths, key=lambda p: p.relative_to(root).as_posix())}


def save(out, name, value):
    (out / name).write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')


def run_gate(root, out, gate):
    name, script, certificate = gate['name'], gate['script'], gate['certificate']
    environment = os.environ.copy()
    environment['PYTHONDONTWRITEBYTECODE'] = '1'
    started = time.monotonic()
    log = out / ('run_v38_' + name + '.log')
    match = False
    declared_pass = False
    error = None
    returncode = None
    try:
        # Missing certificates are failures; there is deliberately no fallback
        # that creates or replaces a certificate from the observed output.
        expected = json.loads((root / 'code' / certificate).read_text(encoding='utf-8'))
        process = subprocess.run([sys.executable, '-B', str(root / 'code' / script)]+gate.get('args',[]),
                                 cwd=root, env=environment, capture_output=True,
                                 text=True, encoding='utf-8')
        returncode = process.returncode
        log.write_text(process.stdout, encoding='utf-8')
        if process.stderr:
            log.with_suffix('.stderr').write_text(process.stderr, encoding='utf-8')
        if process.returncode != 0:
            error = 'Verifier returned a nonzero exit status; inspect the saved log.'
        else:
            actual = json.loads(process.stdout)
            match = actual == expected
            # Preserve each committed certificate's documented status schema.
            expected_status = 'PASS'
            declared_pass = isinstance(actual, dict) and actual.get('status') == expected_status
            if not match:
                error = 'Complete JSON stdout differs from stored certificate; no certificate was rewritten.'
            elif not declared_pass:
                error = 'The certificate does not declare its expected success status.'
    except (ValueError, OSError) as exc:
        error = 'Verifier or certificate comparison failed: ' + str(exc)
        if not log.exists():
            log.write_text(error + '\n', encoding='utf-8')
    return {
        'name': name,
        'generation': gate['generation'],
        'script': 'code/' + script,
        'certificate': 'code/' + certificate,
        'returncode': returncode,
        'certificate_stdout_match': match,
        'certificate_declares_pass': declared_pass,
        'passed': returncode == 0 and match and declared_pass,
        'seconds': round(time.monotonic() - started, 4),
        'log': log.relative_to(root).as_posix(),
        'error': error,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bundle-root', type=Path,
                        default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    root = args.bundle_root.resolve()
    out = root / 'verification'
    if not (root / 'code').is_dir():
        parser.error('The selected bundle root does not contain code/.')
    sys.dont_write_bytecode = True
    out.mkdir(exist_ok=True)
    before = snapshot(root)
    save(out, 'verification_v38_input_sha256.json', before)
    dependency_error = None
    try:
        sympy_version = importlib.metadata.version('sympy')
        flint_version = importlib.metadata.version('python-flint')
        if flint_version != '0.9.0':
            dependency_error = 'Expected python-flint 0.9.0; found ' + flint_version
        if sympy_version != '1.14.0':
            dependency_error = 'Expected SymPy 1.14.0; found ' + sympy_version
    except importlib.metadata.PackageNotFoundError:
        sympy_version = None
        dependency_error = 'SymPy 1.14.0 is required for the symbolic v38 gates.'
    if dependency_error is None:
        with ThreadPoolExecutor(max_workers=3) as pool:
            gates = list(pool.map(lambda g: run_gate(root, out, g), GATES))
    else:
        gates = []
    after = snapshot(root)
    integrity = {
        'version': 38,
        'unchanged': before == after,
        'files_before': len(before),
        'files_after': len(after),
        'changed_files': sorted(n for n in before.keys() & after.keys() if before[n] != after[n]),
        'added_files': sorted(after.keys() - before.keys()),
        'removed_files': sorted(before.keys() - after.keys()),
        'scope': ('Every code directory under the bundle, all Python source including '
                  'independent audit scripts, certificate JSON files, explicit input '
                  'directories, and the original extension inputs; Python bytecode excluded.'),
    }
    report = {
        'version': 38,
        'expected_gate_count': len(GATES),
        'main_gate_count': len(gates),
        'new_gate_count': sum(g['generation'] == 'new_v38' for g in gates),
        'reused_gate_count': sum(g['generation'] == 'reused_v33' for g in gates),
        'gates': gates,
        'all_selected_gates_passed': len(gates) == len(GATES) and all(g['passed'] for g in gates),
        'all_certificates_matched': len(gates) == len(GATES) and all(g['certificate_stdout_match'] for g in gates),
        'code_and_input_integrity_passed': integrity['unchanged'],
        'certificate_regeneration_requested': False,
        'arithmetic': 'Exact rational arithmetic and symbolic polynomial identities; standard library, SymPy 1.14.0 and python-flint 0.9.0.',
        'sympy_version': sympy_version,
        'python_flint_version': importlib.metadata.version('python-flint'),
        'dependency_error': dependency_error,
        'historical_gates_reexecuted': [],
        'historical_gate_reason': 'No historical gate is reexecuted; the five new v38 results have dedicated gates.',
        'mathematical_scope': ('The universal symbolic identities and exact certificates are '
                              'checked. Finite-weight samples supplement the manuscript structural '
                              'proof; they are not an inference of the all-m theorem.'),
    }
    save(out, 'verification_v38_after_sha256.json', after)
    save(out, 'verification_v38_integrity.json', integrity)
    save(out, 'verification_v38.json', report)
    print(json.dumps({'report': report, 'integrity': integrity}, ensure_ascii=False, indent=2))
    if not report['all_selected_gates_passed'] or not integrity['unchanged']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
