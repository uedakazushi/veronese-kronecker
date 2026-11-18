"""Build revised paper X, new paper XI and the research notes; --all also rebuilds inherited papers."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent
PAPERS = ROOT/'papers'
OUT = ROOT/'verification'
OUT.mkdir(exist_ok=True)
REVISED = ['quantum_categories_ja_v40', 'quantum_primitive_spectra_ja_v40', 'vk_research_notes_ja_v40']
INHERITED = ['vk_canonical_deformations_ja_v22', 'fano72_point_configurations_ja_v26', 'relative_critical_corank2_ja_v25', 'nc_cy_resonance_ja_v22', 'self_opposite_prym_fibrations_ja_v30', 'prym_net_arithmetic_ja_v30', 'sextic_prym_septic_covers_ja_v30', 'vk_ambient_completions_ja_v32', 'weighted_poisson_components_ja_v34']
CACHE = Path(os.environ.get('VK_TEX_CACHE', str(Path(tempfile.gettempdir())/'vk_lualatex_v40_cache')))
CACHE.mkdir(parents=True, exist_ok=True)
ENV = os.environ.copy()
ENV.update(TEXMFVAR=str(CACHE), TEXMFCACHE=str(CACHE))


def metadata(stem, path=None):
    path = path or PAPERS/(stem+'.pdf')
    text = subprocess.run(['pdfinfo',str(path)],text=True,capture_output=True,check=True).stdout
    return {'document':stem,
            'pages':int(re.search(r'^Pages:\s+(\d+)',text,re.M).group(1)),
            'bytes':path.stat().st_size,
            'pdf_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}


def build(stem):
    start = time.monotonic()
    passes = []
    # Build with fresh auxiliaries, and publish only a complete validated PDF.
    # A failed or interrupted TeX pass must not truncate a deliverable.
    with tempfile.TemporaryDirectory(prefix='vk_'+stem+'_') as temp:
        staging = Path(temp)
        for source in PAPERS.glob('*.tex'):
            shutil.copy2(source, staging/source.name)
        for index in range(1,4):
            path = OUT/f'build_{stem}_pass{index}.log'
            with path.open('w') as stream:
                proc = subprocess.run(['lualatex','-interaction=nonstopmode','-halt-on-error',stem+'.tex'],
                                      cwd=staging,env=ENV,stdout=stream,stderr=subprocess.STDOUT)
            passes.append(proc.returncode)
            if proc.returncode:
                return {'document':stem,'status':'failed','passes':passes,'log':str(path.relative_to(ROOT))}
        content = (staging/(stem+'.log')).read_text(errors='replace')
        warnings = [line for line in content.splitlines() if any(key in line for key in
                    ['Overfull','LaTeX Warning: Reference','LaTeX Warning: Citation',
                     'There were undefined','Missing character','multiply defined'])]
        result = metadata(stem, staging/(stem+'.pdf'))
        staged_final = PAPERS/('.'+stem+'.pdf.ready')
        shutil.copyfile(staging/(stem+'.pdf'), staged_final)
        assert hashlib.sha256(staged_final.read_bytes()).hexdigest() == result['pdf_sha256']
        os.replace(staged_final, PAPERS/(stem+'.pdf'))
        assert hashlib.sha256((PAPERS/(stem+'.pdf')).read_bytes()).hexdigest() == result['pdf_sha256']
    result.update(status='passed',passes=passes,tex_warnings_requiring_review=warnings,
                  seconds=round(time.monotonic()-start,3), atomic_pdf_publication=True)
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--all',action='store_true')
    parser.add_argument('--document',choices=REVISED+INHERITED,action='append')
    args = parser.parse_args()
    selected = args.document or REVISED+(INHERITED if args.all else [])
    with ThreadPoolExecutor(max_workers=2) as pool:
        results = list(pool.map(build,selected))
    report_path = OUT/'build_v40.json'
    prior = json.loads(report_path.read_text())['documents'] if report_path.exists() else []
    combined = {row['document']:row for row in prior}
    combined.update({row['document']:row for row in results})
    report = {'engine':'LuaLaTeX','documents':list(combined.values()),
              'inherited_without_rebuild':[metadata(stem) for stem in INHERITED if stem not in combined]}
    report_path.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(report,ensure_ascii=False,indent=2))
    if any(row['status']!='passed' for row in results):
        raise SystemExit(1)
