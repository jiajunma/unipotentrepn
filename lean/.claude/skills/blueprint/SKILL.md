---
name: blueprint
description: "Generate informal proof blueprints for mathematical theorems. Reads paper PDFs, existing Lean formalization, and produces structured markdown blueprints suitable for Lean formalization. Use when the user asks to generate a blueprint, plan a proof, or analyze a theorem from a paper before formalization. Supports mid-project entry — can read existing Lean code to understand what's already proved."
---

# Blueprint: Informal Proof Blueprint Generator

Generate structured informal proof blueprints for mathematical theorems, designed for subsequent Lean 4 formalization. Adapted from [Rethlas](https://github.com/frenzymath/Rethlas) reasoning patterns for Claude Code.

## When to Use

- User asks to generate a blueprint / proof plan for a theorem
- User wants to analyze a paper theorem before formalization
- User says `/blueprint` followed by a theorem reference
- User wants a non-formal proof sketch organized for Lean translation

## Invocation

```
/blueprint <target>
```

Where `<target>` is one of:
- A theorem reference: `Lemma 11.5 of [BMSZ]`
- A file path to a PDF: `papers/BMSZ_construction_unitarity.pdf pages 64-65`
- A Lean sorry: `CombUnipotent/MYD.lean:523`
- A mathematical statement in natural language

## Core Principles

1. **Read before writing.** Always read the paper source AND existing Lean code first.
2. **Context-aware.** Identify what's already formalized — don't re-derive proved facts.
3. **Lean-oriented.** Structure the blueprint so each section maps to a Lean declaration.
4. **Dependency-explicit.** State exactly which prior results each step uses.
5. **Failure-honest.** Flag steps that seem hard to formalize and explain why.

## Workflow

### Phase 1: Context Gathering

1. **Read the paper.** If a PDF path is given, read the relevant pages. Extract:
   - The exact theorem statement
   - The proof in the paper
   - All referenced lemmas, propositions, definitions
   - Notation conventions

2. **Read existing Lean code.** Scan the project for:
   - What's already formalized (grep for the theorem name, related definitions)
   - Available infrastructure (types, lemmas, tactics)
   - Current sorry locations (what's missing)
   - Naming conventions used in the project

3. **Build a dependency graph.** For each result the theorem depends on:
   - Is it already in Lean? → note the declaration name
   - Is it in Mathlib? → search with lean_leansearch / lean_loogle
   - Does it need to be proved first? → flag as prerequisite

### Phase 2: Decomposition

Apply Rethlas-style subgoal decomposition:

1. **Immediate consequences.** What follows directly from definitions?
2. **Case analysis.** Does the proof split into cases? List them.
3. **Induction structure.** Is there an induction? On what? What's the inductive step?
4. **Key lemmas.** What are the non-trivial intermediate steps?
5. **Combinatorial/algebraic core.** What's the hard mathematical content?

For each subgoal, classify:
- `trivial` — follows from definitions or simple case analysis
- `routine` — standard argument, should be straightforward in Lean
- `nontrivial` — requires real mathematical insight
- `hard` — may need significant Lean infrastructure or creative tactics
- `already-proved` — exists in the Lean codebase or Mathlib

### Phase 3: Blueprint Generation

Write the blueprint in structured markdown format:

```markdown
# Blueprint: [Theorem Name]

## Source
[Paper reference, page numbers, equation numbers]

## Statement
[Precise mathematical statement]

## Dependencies
- [Dep 1]: [status: formalized/mathlib/needs-proof]
- [Dep 2]: ...

## Lean Target
```lean
theorem theorem_name ... : ... := by
  sorry
```

## Proof Plan

### Step 1: [Description]
**Difficulty**: trivial/routine/nontrivial/hard
**Uses**: [list of dependencies]
**Lean sketch**:
```lean
-- tactic sketch
```
**Informal argument**: ...

### Step 2: ...
...

## Risks and Alternatives
- [What might go wrong in formalization]
- [Alternative approaches if the main plan fails]
```

### Phase 4: Self-Check

Before outputting, verify:
- [ ] Every step cites its dependencies
- [ ] No circular dependencies
- [ ] Already-proved results are correctly referenced with Lean names
- [ ] The step decomposition covers the full proof
- [ ] Hard steps are flagged with mitigation strategies

## Output

Write the blueprint to `docs/blueprints/<theorem_name>.md` in the project.

If the theorem is part of a batch (e.g., "all theorems from Section 11"), create one file per major theorem and an index file `docs/blueprints/INDEX.md`.

## Adaptation for Mid-Project Entry

When the project already has substantial formalization:

1. **Inventory existing code first.** Run:
   ```
   grep -rn 'theorem\|lemma\|def' CombUnipotent/ --include='*.lean'
   ```
   to see what's available.

2. **Check sorry locations.** Run:
   ```
   grep -rn 'sorry' CombUnipotent/ --include='*.lean'
   ```
   to see what's missing.

3. **Map paper references to Lean names.** Many paper results already have Lean counterparts with different names. Build this mapping explicitly.

4. **Identify the frontier.** The blueprint should focus on theorems at the boundary between "formalized" and "not yet formalized" — these are the ones most ready for proof.

## Batch Mode

For processing multiple related theorems (e.g., a whole section of a paper):

1. Read the entire section first
2. Build a complete dependency graph across all theorems
3. Topologically sort by dependencies
4. Generate blueprints in dependency order
5. Mark which ones can be parallelized (independent dependencies)

## Example Invocation

```
/blueprint Lemma 11.5 from papers/BMSZ_construction_unitarity.pdf pages 64
```

This would:
1. Read page 64 of the PDF
2. Extract Lemma 11.5's statement and proof
3. Check CombUnipotent/MYD.lean for existing AC/theta-lift infrastructure
4. Generate a decomposed blueprint targeting Lean formalization
