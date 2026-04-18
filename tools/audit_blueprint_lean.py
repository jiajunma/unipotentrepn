#!/usr/bin/env python3
"""
Audit blueprint ↔ Lean alignment.

Three categories:
  A. DOMAIN-ONLY  (definition or theorem whose subject is its input type)
     — takes τ : PBP, or source : ACResult, or E : ILS, possibly with shape
       hypotheses (hγ, h_tail, h_sub, h_prim, etc). This is *unconditional*.

  B. EXTRA-HYPOTHESIS  (theorem takes named proof objects beyond subject)
     — e.g. `h_fc`, `h_sign`, `h_std`, `h_pt`, `h_eq`, `h_first`, etc.
     These are *conditional* and flagged.

  C. NOT-FOUND         (blueprint references a name that doesn't exist)
"""
from __future__ import annotations

import json
import re
from pathlib import Path

# These named hypothesis prefixes indicate extra proof assumptions
# (NOT the natural domain/shape input).
EXTRA_HYP_PATTERNS = [
    r'\bh_fc\b\s*:',
    r'\bh_sign\b\s*:',
    r'\bh_fcSign\b\s*:',
    r'\bh_std\b\s*:',
    r'\bh_pt\b\s*:',
    r'\bh_qt\b\s*:',
    r'\bh_first\b',
    r'\bh_first_entry\b',
    r'\bh_prop_11_4\b',
    r'\bh_prop_11_4_p\b',
    r'\bh_prop_11_4_q\b',
    r'\bh_eq\b\s*:.*(twistBD|charTwistCM|augment)',
    r'\bh_inner\b',
    r'\bh_lift_ok\b',
    r'\bh_dsum\b',
    r'\bh_descent\b',
    r'\bh_residual\b',
    r'\bh_shape_identity\b',
    r'\bh_n₀\b',
    r'\bh_n_0\b',
    r'\bh_ne\b\s*:',
    r'\bsource_sig\b',
    r'\bsource_fcSig\b',
    r'\bn_prev\b.*:\s*ℤ',
    r'\bp_prev\b.*:\s*ℤ',
    r'\bq_prev\b.*:\s*ℤ',
    r'\bn_inner\b.*:\s*ℤ',
]

LEAN_REF_RE = re.compile(r'\\lean\{([^}]+)\}')

def extract_sig(lean_file: Path, line: int, max_lines: int = 40) -> str:
    try:
        text = lean_file.read_text(encoding='utf-8')
    except Exception:
        return ''
    lines = text.splitlines()
    start = max(0, line - 1)
    out = []
    depth = 0
    for i in range(start, min(len(lines), start + max_lines)):
        ln = lines[i]
        out.append(ln)
        for ch in ln:
            if ch == '(': depth += 1
            elif ch == ')': depth -= 1
            elif ch == '{': depth += 1
            elif ch == '}': depth -= 1
            elif ch == '[': depth += 1
            elif ch == ']': depth -= 1
        s = ln.rstrip()
        if depth == 0 and (s.endswith(':= by') or re.search(r':=\s*$', s) or
                           re.search(r':= [^=]', s) or
                           re.match(r'^\s*(theorem|lemma|def|noncomputable|@)', lines[i+1] if i+1 < len(lines) else '')):
            break
    return '\n'.join(out)

def classify(sig: str) -> tuple[str, list[str]]:
    flagged = []
    for pat in EXTRA_HYP_PATTERNS:
        for m in re.finditer(pat, sig):
            flagged.append(m.group(0))
    return (('extra-hyp', sorted(set(flagged))) if flagged else ('domain-only', []))

def main() -> int:
    repo = Path(__file__).parent.parent
    blueprint = repo / 'lean/blueprint/src/chapters'
    decls_path = repo / 'docs/blueprint/find/lean_decls.json'

    with open(decls_path) as f:
        decls_data = json.load(f)
    decls = decls_data['decls']

    refs = []
    for tex_file in sorted(blueprint.glob('*.tex')):
        text = tex_file.read_text()
        for block in re.finditer(
            r'\\begin\{(lemma|proposition|theorem|corollary|definition)\}[^\n]*\n(.*?)\\end\{\1\}',
            text, re.DOTALL,
        ):
            body = block.group(2)
            label_m = re.search(r'\\label\{([^}]+)\}', body)
            if not label_m: continue
            label = label_m.group(1)
            leanok = bool(re.search(r'\\leanok\b', body))
            for lm in LEAN_REF_RE.finditer(body):
                for name in (s.strip() for s in lm.group(1).split(',')):
                    if name:
                        refs.append({
                            'tex': tex_file.name, 'label': label,
                            'name': name, 'leanok': leanok,
                            'env': block.group(1),
                        })

    domain_only, extra_hyp, not_found = 0, 0, 0
    issues: dict[str, list[dict]] = {}

    for ref in refs:
        decl = decls.get(ref['name'])
        if not decl:
            not_found += 1
            continue
        lean_file = repo / decl['file']
        sig = extract_sig(lean_file, decl['line'])
        cat, flags = classify(sig)
        ref['category'] = cat
        ref['flags'] = flags
        if cat == 'domain-only':
            domain_only += 1
        else:
            extra_hyp += 1
            issues.setdefault(ref['label'], []).append(ref)

    print(f'=== Blueprint ↔ Lean audit ===')
    print(f'Total refs: {len(refs)}')
    print(f'  DOMAIN-ONLY (unconditional, takes only τ/source/E + shape hyps): {domain_only}')
    print(f'  EXTRA-HYP   (takes h_fc/h_sign/h_std/h_eq/h_first/h_pt etc): {extra_hyp}')
    print(f'  NOT-FOUND: {not_found}')
    print()

    if issues:
        print(f'=== Extra-hypothesis labels ({len(issues)}) ===')
        for label, rs in sorted(issues.items()):
            kind = rs[0]['env']
            names = ', '.join(r['name'] for r in rs)
            flags = sorted({f for r in rs for f in r['flags']})
            print(f'[{kind}] {label}')
            print(f'    Lean: {names}')
            print(f'    Extra hyps: {", ".join(flags)}')
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
