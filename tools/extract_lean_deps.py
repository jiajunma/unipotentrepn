#!/usr/bin/env python3
"""
Extract programmatic dependency graph from Lean source.

For each theorem/lemma in lean/CombUnipotent/, parse the proof body and
extract identifiers that match other declared theorem names. Output a JSON
mapping: theorem_name → [list of dependencies].

Then cross-reference with blueprint `\\lean{...}` annotations to derive a
label-level dependency graph that can be compared against the blueprint's
manually-written `\\uses{...}` directives.

Usage:
    python3 tools/extract_lean_deps.py \\
        --decls docs/blueprint/find/lean_decls.json \\
        --blueprint lean/blueprint/src/chapters \\
        --out lean_deps.json
"""
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

# ----------------------------------------------------------------------------
# Lean source parsing
# ----------------------------------------------------------------------------

# Identifier pattern (allowing dots, underscores, primes, digits, unicode)
IDENT_RE = re.compile(r'\b([A-Za-z_][A-Za-z_0-9.\u0370-\u1FFF\u2070-\uFFFF]*)\b')

# Pattern that opens a theorem/def block. We capture the body up to the next
# top-level declaration.
DECL_OPEN_RE = re.compile(
    r'^(?:private\s+|protected\s+|noncomputable\s+|@\[[^\]]*\]\s*)*'
    r'(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque)\s+([\w\.]+)',
    re.MULTILINE,
)


NAMESPACE_OPEN_RE = re.compile(r'^namespace\s+([\w\.]+)', re.MULTILINE)
NAMESPACE_END_RE = re.compile(r'^end\s+([\w\.]+)', re.MULTILINE)


def _blank_out_block_comments(text: str) -> str:
    """Replace /- ... -/ (including docstrings /-- -/ and module comments /-! -/)
    with equal-length whitespace, preserving line numbers and keyword boundaries.

    Without this, a block comment containing a keyword like `class` or `def` on
    its own line would trigger a spurious DECL_OPEN_RE match, truncating the
    preceding decl's body and leaving comment fragments in the output.
    """
    def _sub(m: re.Match) -> str:
        return ''.join('\n' if c == '\n' else ' ' for c in m.group(0))
    return re.sub(r'/-.*?-/', _sub, text, flags=re.DOTALL)


def split_into_decl_bodies(text: str) -> list[tuple[str, str, list[str]]]:
    """Return a list of (decl_name, body_text, namespace_stack) per decl.

    namespace_stack is the active `namespace X ... end X` stack at that point,
    so a decl `foo` inside `namespace ILS` resolves to `ILS.foo`.
    """
    # Strip block comments globally BEFORE any regex matching so that decl
    # detection can't trip on a keyword appearing inside a comment.
    text = _blank_out_block_comments(text)
    events: list[tuple[int, str, object]] = []
    for m in NAMESPACE_OPEN_RE.finditer(text):
        events.append((m.start(), 'open', m.group(1)))
    for m in NAMESPACE_END_RE.finditer(text):
        events.append((m.start(), 'end', m.group(1)))
    decl_matches = list(DECL_OPEN_RE.finditer(text))
    for i, m in enumerate(decl_matches):
        events.append((m.start(), 'decl', i))
    events.sort(key=lambda e: e[0])

    stack: list[str] = []
    bodies: list[tuple[str, str, list[str]]] = []
    for pos, kind, payload in events:
        if kind == 'open':
            stack.append(payload)
        elif kind == 'end':
            if stack and stack[-1] == payload:
                stack.pop()
        else:
            i = payload
            m = decl_matches[i]
            name = m.group(1)
            start = m.start()
            end = decl_matches[i + 1].start() if i + 1 < len(decl_matches) else len(text)
            bodies.append((name, text[start:end], list(stack)))
    return bodies


def extract_referenced_idents(body: str) -> set[str]:
    """Extract all identifiers in a decl body.

    NOTE: caller (`build_lean_dep_graph` via `split_into_decl_bodies`) has
    already stripped block comments at the file level, so we only need to
    handle line comments and strings here.
    """
    # Strip line comments (-- ...)
    body = re.sub(r'--[^\n]*', '', body)
    # Strip string literals (rough)
    body = re.sub(r'"[^"]*"', '', body)
    # Strip the header up to first `:=` — proof/def body follows.
    if ':=' in body:
        body = body.split(':=', 1)[1]
    return set(IDENT_RE.findall(body))


# ----------------------------------------------------------------------------
# Build dependency graph
# ----------------------------------------------------------------------------

def resolve_token(
    tok: str,
    ns_stack: list[str],
    full_names: set[str],
    short_to_full: dict[str, list[str]],
) -> list[str]:
    """Resolve a source token to zero, one, or multiple full declaration names.

    Priority:
      1. tok itself is a full name (e.g., "ILS.thetaLift_CD"). Return just that.
      2. tok is a short name; try each namespace prefix (deepest first) so
         `augment` inside `namespace ILS` resolves to `ILS.augment` when it
         exists. Return just that if found.
      3. short-name lookup: return ALL candidates. Transitive closure through
         unlabeled wrappers will filter to the subset that's actually labeled.
    """
    if tok in full_names:
        return [tok]
    for depth in range(len(ns_stack), 0, -1):
        prefix = '.'.join(ns_stack[:depth])
        candidate = f'{prefix}.{tok}'
        if candidate in full_names:
            return [candidate]
    # Compound tokens like `twisted.thetaLift` (Lean 4 method-call syntax):
    # try the last segment as a short name.
    if '.' in tok:
        short = tok.rsplit('.', 1)[1]
        if short in short_to_full:
            return list(short_to_full[short])
    return list(short_to_full.get(tok, []))


def build_lean_dep_graph(
    repo: Path,
    decls: dict,
    labeled_names: set[str] | None = None,
) -> dict[str, list[str]]:
    """For each known declaration, list which OTHER known declarations it
    transitively references via unlabeled wrappers.

    If `labeled_names` is given, traversal stops at any labeled decl (those
    become the direct deps). Unlabeled decls are expanded, so a wrapper
    `AC.step = match γ with | .D => step_D_impl` correctly surfaces
    `step_D_impl`'s labeled deps (e.g. `ILS.thetaLift_CD`) at `AC.step`.
    """
    # Index by short name. Exclude short-name aliases (entries whose name has
    # no dot but whose file/line matches a qualified entry) so resolution
    # returns canonical qualified forms only.
    qualified = {n for n in decls if '.' in n}
    # Identify short-name aliases: unqualified entries whose (file, line) matches
    # exactly one qualified entry.
    qualified_by_loc: dict[tuple[str, int], str] = {}
    for n in qualified:
        info = decls[n]
        qualified_by_loc[(info['file'], info['line'])] = n
    alias_names: set[str] = set()
    for n, info in decls.items():
        if '.' not in n:
            canonical = qualified_by_loc.get((info['file'], info['line']))
            if canonical and canonical != n:
                alias_names.add(n)
    full_names = set(decls.keys()) - alias_names
    short_to_full: dict[str, list[str]] = {}
    for full_name in full_names:
        short_to_full.setdefault(full_name.split('.')[-1], []).append(full_name)
    if labeled_names is None:
        labeled_names = full_names  # no transitive closure

    # First pass: direct refs only (no transitive closure yet).
    # Skip alias entries — they point to the same row as a qualified name and
    # would be orphaned because declaration bodies only match qualified names.
    direct: dict[str, set[str]] = {}
    for full_name, info in decls.items():
        if full_name in alias_names:
            continue
        path = repo / info['file']
        try:
            text = path.read_text(encoding='utf-8')
        except Exception:
            continue
        for d_name, body, ns_stack in split_into_decl_bodies(text):
            # Match by full name: either ns_stack + d_name equals full_name,
            # or d_name already IS full_name (no namespace).
            candidate = '.'.join(ns_stack + [d_name]) if ns_stack else d_name
            if candidate != full_name:
                continue
            idents = extract_referenced_idents(body)
            referenced: set[str] = set()
            for tok in idents:
                for resolved in resolve_token(tok, ns_stack, full_names, short_to_full):
                    if resolved != full_name:
                        referenced.add(resolved)
            direct[full_name] = referenced
            break

    # Second pass: transitive closure through unlabeled decls.
    # For each decl, expand any dep that's unlabeled (and different from self)
    # into its own deps, up to a depth cap.
    deps: dict[str, list[str]] = {}
    for name, refs in direct.items():
        visited: set[str] = set()
        stack: list[str] = list(refs)
        result: set[str] = set()
        while stack:
            cur = stack.pop()
            if cur in visited or cur == name:
                continue
            visited.add(cur)
            if cur in labeled_names:
                result.add(cur)
            else:
                # Unlabeled wrapper: expand its own direct deps
                for sub in direct.get(cur, set()):
                    if sub not in visited:
                        stack.append(sub)
        deps[name] = sorted(result)

    return deps


# ----------------------------------------------------------------------------
# Map to blueprint label graph
# ----------------------------------------------------------------------------

LEAN_REF_RE = re.compile(r'\\lean\{([^}]+)\}')
LABEL_RE = re.compile(r'\\label\{([^}]+)\}')
USES_RE = re.compile(r'\\uses\{([^}]+)\}')
ENV_OPEN_RE = re.compile(r'\\begin\{(lemma|proposition|theorem|corollary|definition)\}', )


def parse_blueprint(chapters: Path) -> tuple[dict[str, list[str]], dict[str, set[str]]]:
    """Return:
       - lean_to_label: each Lean name → blueprint label that references it
       - label_uses:    each blueprint label → declared \\uses{...} set"""
    lean_to_label: dict[str, list[str]] = {}
    label_uses: dict[str, set[str]] = {}
    for tex in chapters.glob('*.tex'):
        text = tex.read_text()
        # Iterate environment blocks
        for m in re.finditer(
            r'\\begin\{(lemma|proposition|theorem|corollary|definition)\}.*?\\end\{\1\}',
            text, re.DOTALL,
        ):
            block = m.group(0)
            label_m = LABEL_RE.search(block)
            if not label_m:
                continue
            label = label_m.group(1)
            for lm in LEAN_REF_RE.finditer(block):
                for n in lm.group(1).split(','):
                    lean_to_label.setdefault(n.strip(), []).append(label)
            uses: set[str] = set()
            for um in USES_RE.finditer(block):
                for u in um.group(1).split(','):
                    uses.add(u.strip())
            label_uses.setdefault(label, set()).update(uses)
    return lean_to_label, label_uses


def derive_label_deps(
    lean_deps: dict,
    lean_to_label: dict,
    decls: dict | None = None,
) -> dict[str, set[str]]:
    """For each blueprint label, derive the set of OTHER labels it depends on
    based on the Lean dependency graph + lean→label mapping.

    Accepts alias Lean names in `lean_to_label` (e.g. blueprint references
    `prop_11_14_PBP_D` which aliases `PBPInstantiation.prop_11_14_PBP_D`);
    such aliases are canonicalized against `decls` (file+line match).
    """
    canonical_map: dict[str, str] = {}
    if decls is not None:
        loc_to_qual: dict[tuple[str, int], str] = {}
        for n, info in decls.items():
            if '.' in n:
                loc_to_qual[(info['file'], info['line'])] = n
        for n, info in decls.items():
            if '.' not in n:
                qual = loc_to_qual.get((info['file'], info['line']))
                if qual and qual != n:
                    canonical_map[n] = qual

    def canon(name: str) -> str:
        return canonical_map.get(name, name)

    label_deps: dict[str, set[str]] = {}
    # Build a reverse index: canonical_lean_name → labels
    canon_to_labels: dict[str, set[str]] = {}
    for lean_name, labels in lean_to_label.items():
        for lab in labels:
            canon_to_labels.setdefault(canon(lean_name), set()).add(lab)

    for lean_name, lean_refs in lean_deps.items():
        labels = canon_to_labels.get(canon(lean_name), set())
        for label in labels:
            for ref_lean in lean_refs:
                ref_labels = canon_to_labels.get(canon(ref_lean), set())
                for r in ref_labels:
                    if r != label:
                        label_deps.setdefault(label, set()).add(r)
    return label_deps


# ----------------------------------------------------------------------------
# Main
# ----------------------------------------------------------------------------

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument('--decls', required=True)
    ap.add_argument('--blueprint', required=True, help='blueprint chapters dir')
    ap.add_argument('--out', required=True, help='output JSON')
    ap.add_argument('--repo-root', default='.')
    args = ap.parse_args()

    repo = Path(args.repo_root).resolve()
    with open(args.decls, encoding='utf-8') as f:
        decls = json.load(f)['decls']

    print(f'[deps] indexing Lean decls: {len(decls)}')

    lean_to_label, label_uses_declared = parse_blueprint(Path(args.blueprint))
    print(f'[deps] blueprint covers {len(lean_to_label)} Lean names → {len(label_uses_declared)} labels')

    labeled_names = set(lean_to_label.keys()) & set(decls.keys())
    lean_deps = build_lean_dep_graph(repo, decls, labeled_names=labeled_names)
    print(f'[deps] extracted Lean dep graph for {len(lean_deps)} decls '
          f'(transitive through {len(decls) - len(labeled_names)} unlabeled wrappers)')

    label_deps_derived = derive_label_deps(lean_deps, lean_to_label, decls)
    print(f'[deps] derived {len(label_deps_derived)} label-level dep sets from Lean')

    # Cross-check: declared `\uses` vs derived
    extra_declared, missing_declared = {}, {}
    for label, derived in label_deps_derived.items():
        declared = label_uses_declared.get(label, set())
        extra = declared - derived  # in \uses but not in Lean
        missing = derived - declared  # in Lean but not in \uses
        if extra:  extra_declared[label] = sorted(extra)
        if missing: missing_declared[label] = sorted(missing)

    out = {
        'lean_deps': lean_deps,
        'lean_to_label': lean_to_label,
        'label_deps_derived_from_lean': {k: sorted(v) for k, v in label_deps_derived.items()},
        'label_uses_declared_in_blueprint': {k: sorted(v) for k, v in label_uses_declared.items()},
        'extra_in_blueprint_uses_not_in_lean': extra_declared,
        'missing_in_blueprint_uses_present_in_lean': missing_declared,
    }
    Path(args.out).write_text(json.dumps(out, ensure_ascii=False, indent=2))
    print(f'[deps] wrote {args.out}')
    print()
    print(f'Audit summary:')
    print(f'  Labels with EXTRA \\uses (declared but not in Lean): {len(extra_declared)}')
    print(f'  Labels with MISSING \\uses (in Lean but not declared): {len(missing_declared)}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
