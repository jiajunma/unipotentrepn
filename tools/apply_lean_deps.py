#!/usr/bin/env python3
"""Apply Lean-derived \\uses{} to blueprint .tex files.

Reads tmp/lean_deps.json (produced by extract_lean_deps.py) and rewrites
the \\uses{} declarations in lean/blueprint/src/chapters/*.tex so that
each labeled statement's dependency set equals the Lean-extracted set.

Strategy:
- For each \\label{KEY}, scan forward (up to statement end) for a \\uses{...}
  macro and replace its contents with the Lean-derived set (sorted).
- If no \\uses{...} exists but Lean has deps, insert one right after the label.
- If Lean has no deps for a label, leave any existing \\uses{...} alone (mathematical
  dependencies that don't surface in Lean syntax may still be valid).

Writes a dry-run diff to stdout by default. Pass --write to apply.
"""
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
USES_RE = re.compile(r"\\uses\{([^}]*)\}")

# Statement environments to scope \uses{} search.
# Matches \begin{...} ... \end{...} for proposition/theorem/lemma/definition-like envs.
ENV_BEGIN_RE = re.compile(r"\\begin\{(definition|theorem|lemma|proposition|corollary|remark|example)\}")
ENV_END_RE = re.compile(r"\\end\{(definition|theorem|lemma|proposition|corollary|remark|example)\}")


def find_label_blocks(text: str) -> list[tuple[int, int, str, str, tuple[int, int] | None]]:
    """Return list of (block_start, block_end, label, env, uses_span).

    block is a statement env; label is the first label inside it; uses_span is
    (start, end) of the \\uses{...} match inside the block, or None.
    """
    lines = text.splitlines(keepends=True)
    # Build offset index
    offsets = [0]
    for line in lines:
        offsets.append(offsets[-1] + len(line))

    results = []
    i = 0
    pos = 0
    while pos < len(text):
        m = ENV_BEGIN_RE.search(text, pos)
        if not m:
            break
        env = m.group(1)
        block_start = m.start()
        # Find matching \end{env} (non-nested; these envs don't nest in practice)
        end_pat = re.compile(r"\\end\{" + env + r"\}")
        em = end_pat.search(text, m.end())
        if not em:
            pos = m.end()
            continue
        block_end = em.end()
        block = text[block_start:block_end]
        lbl_m = LABEL_RE.search(block)
        if lbl_m:
            label = lbl_m.group(1)
            uses_m = USES_RE.search(block)
            uses_span = None
            if uses_m:
                uses_span = (block_start + uses_m.start(), block_start + uses_m.end())
            results.append((block_start, block_end, label, env, uses_span))
        pos = block_end
    return results


def derive_label_uses(lean_deps: dict) -> dict[str, list[str]]:
    """Return {label: sorted_list_of_dep_labels}."""
    derived = lean_deps.get("label_deps_derived_from_lean", {})
    out = {}
    for lbl, deps in derived.items():
        # deps may include self-references; filter
        cleaned = sorted(set(d for d in deps if d != lbl))
        out[lbl] = cleaned
    return out


def apply_to_file(
    path: Path,
    derived: dict[str, list[str]],
    write: bool,
    mode: str = "union",
) -> list[str]:
    """Apply derived \\uses{} to path. Returns list of human-readable diffs.

    mode="union"   : new = OLD ∪ Lean-derived (preserves mathematical deps that
                     the syntactic extractor can't see — recommended default).
    mode="replace" : new = Lean-derived only (aggressive; drops deps whose
                     targets don't surface in the Lean proof body).
    """
    text = path.read_text()
    blocks = find_label_blocks(text)
    diffs: list[str] = []
    edits: list[tuple[int, int, str]] = []
    for block_start, block_end, label, env, uses_span in blocks:
        new_deps = derived.get(label)
        if new_deps is None:
            continue  # label not covered by Lean; leave alone
        # Union with existing declared uses if mode=union
        if mode == "union" and uses_span is not None:
            old_content = text[uses_span[0]:uses_span[1]]
            om = USES_RE.match(old_content)
            if om:
                old_set = {t.strip() for t in om.group(1).split(",") if t.strip()}
                merged = sorted(set(new_deps) | old_set)
                new_deps = [d for d in merged if d != label]
        new_uses = "\\uses{" + ", ".join(new_deps) + "}"
        if uses_span is not None:
            old_uses = text[uses_span[0]:uses_span[1]]
            if old_uses != new_uses:
                diffs.append(f"  [{env}] {label}:\n    OLD: {old_uses}\n    NEW: {new_uses}")
                edits.append((uses_span[0], uses_span[1], new_uses))
        else:
            if new_deps:
                # Insert \uses{} right after the \label{} line
                block = text[block_start:block_end]
                lbl_m = LABEL_RE.search(block)
                if lbl_m:
                    insert_pos = block_start + lbl_m.end()
                    # Find indentation of the \label line
                    line_start = text.rfind("\n", 0, insert_pos) + 1
                    indent_match = re.match(r"[ \t]*", text[line_start:insert_pos])
                    indent = indent_match.group(0) if indent_match else ""
                    insertion = "\n" + indent + new_uses
                    diffs.append(f"  [{env}] {label}:\n    OLD: (none)\n    NEW: {new_uses}")
                    edits.append((insert_pos, insert_pos, insertion))
    # In replace mode, handle the case where Lean has empty deps but blueprint
    # has \uses{...}: aggressive mode → delete the \uses{} macro entirely.
    for block_start, block_end, label, env, uses_span in blocks:
        if mode != "replace":
            continue
        new_deps = derived.get(label)
        if new_deps == [] and uses_span is not None:
            old_uses = text[uses_span[0]:uses_span[1]]
            diffs.append(f"  [{env}] {label}:\n    OLD: {old_uses}\n    NEW: (removed — Lean has no deps)")
            # Remove the \uses{} macro + its leading whitespace on the same line if that's all
            ls = text.rfind("\n", 0, uses_span[0]) + 1
            le_after = text.find("\n", uses_span[1])
            line_content = text[ls:uses_span[0]] + text[uses_span[1]:le_after if le_after >= 0 else len(text)]
            if line_content.strip() == "":
                # Remove entire line including its trailing \n
                real_end = (le_after + 1) if le_after >= 0 else len(text)
                edits.append((ls, real_end, ""))
            else:
                edits.append((uses_span[0], uses_span[1], ""))

    if not edits:
        return diffs

    # Deduplicate / sort edits by start descending; skip overlapping duplicates
    edits.sort(key=lambda e: e[0], reverse=True)
    seen = set()
    unique_edits = []
    for start, end, repl in edits:
        key = (start, end)
        if key in seen:
            continue
        seen.add(key)
        unique_edits.append((start, end, repl))

    new_text = text
    for start, end, repl in unique_edits:
        new_text = new_text[:start] + repl + new_text[end:]

    if write:
        path.write_text(new_text)

    return diffs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--deps", default="tmp/lean_deps.json")
    ap.add_argument("--chapters", default="lean/blueprint/src/chapters")
    ap.add_argument("--write", action="store_true", help="Apply changes; otherwise dry-run")
    ap.add_argument("--mode", choices=["union", "replace"], default="union",
                    help="union: new = OLD ∪ Lean-derived (safe). replace: new = Lean-derived only (aggressive).")
    args = ap.parse_args()

    with open(args.deps) as f:
        lean_deps = json.load(f)
    derived = derive_label_uses(lean_deps)

    chapters = sorted(Path(args.chapters).glob("*.tex"))
    total_diffs = 0
    for p in chapters:
        diffs = apply_to_file(p, derived, write=args.write, mode=args.mode)
        if diffs:
            print(f"\n=== {p} ===")
            for d in diffs:
                print(d)
            total_diffs += len(diffs)

    print(f"\n[apply_lean_deps] {total_diffs} label(s) changed, write={args.write}")


if __name__ == "__main__":
    main()
