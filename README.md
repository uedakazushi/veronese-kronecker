# Veronese–Kronecker / Loginov–Orlov research

2026-11-19 — source consolidation from the v40 research bundle (2026-10-30).

This repository collects the noncommutative Veronese–Kronecker, Loginov–Orlov and Fano degree 72 research, including deformations, weighted ambient geometry, Prym geometry, covers, quantum categories, primitive spectra, and verification code.

- `papers/`: Japanese LuaLaTeX sources, preferring the latest version of each independent document/section. Earlier source variants are retained only where current LaTeX explicitly references them.
- `code/`: currently useful Python source files, with a lightweight selection of current-era checks.
- `build_v40.py`: original bundle build script. It may expect further verification assets and has not been revalidated after the repository extraction.

**Status:** This is a preservation and source-organization import, not a fresh mathematical audit. Statements should be evaluated using each manuscript's explicit hypotheses and verification status. The original v40 ZIP in ChatGPT Library contains additional historical artifacts, PDF renders, detailed certificates and audit data, which are not Git-tracked here. No PDF is tracked; compile locally with LuaLaTeX, luatexja and HaranoAji fonts.

For a main manuscript, use the matching `papers/*_ja_vXX.tex` and its `\input` dependencies. Where a file is a section fragment, compile its parent manuscript instead. Generated outputs and cached LaTeX files are ignored.
