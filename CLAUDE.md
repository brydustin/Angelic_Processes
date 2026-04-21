# Rules for Working on the Isabelle/HOL Formalization (Angelic_Processes)

These rules describe how to work in **this Isabelle project**, whose main theory is:

- **Theory:** `Angelic_Processes`
- **Imports:** `UTP2.utp`
  - Do **not** import `Complex_Main` directly — it is pulled in transitively through UTP2.
- **Source to formalize:** `/home/dusty/Desktop/Isabelle/project/main.tex`

### Path reference (use these exactly — never abbreviate)

| Item | Path |
|---|---|
| Project directory | `/home/dusty/Desktop/Isabelle/project` |
| Isabelle binary | `/home/dusty/Desktop/Isabelle/project/Isabelle2025-2/bin/isabelle` |
| UTP session | `UTP2` |
| UTP entry theory | `utp` |
| UTP source | `/home/dusty/Desktop/Isabelle/project/UTP-main/` |
| Abstract_Prog_Syntax | `/home/dusty/Desktop/Isabelle/project/Abstract_Prog_Syntax-main/` |
| Z_Toolkit | `/home/dusty/Desktop/Isabelle/project/Z_Toolkit-main/` |
| Definition prefix | `ap_` |

---

## 0. Before You Start: Verify the Environment

Run these checks once at the start of every session before touching any
theory files.

### Step 1 — confirm the CLI tools are installed
```bash
/home/dusty/Desktop/Isabelle/project/Isabelle2025-2/bin/isabelle eval_at
/home/dusty/Desktop/Isabelle/project/Isabelle2025-2/bin/isabelle desorry
```
Both must print usage text. If either says "Unknown Isabelle tool", run:
```bash
bash /home/dusty/Desktop/Isabelle/project/isa_agentic_cli_tools-main/isa_cli_tools/install.sh \
  /home/dusty/Desktop/Isabelle/project/Isabelle2025-2
```
Then retry. **Do not proceed until both tools are available.**

### Step 2 — confirm UTP2 builds
```bash
/home/dusty/Desktop/Isabelle/project/Isabelle2025-2/bin/isabelle build \
  -d /home/dusty/Desktop/Isabelle/project \
  -v UTP2
```
If this fails, **stop and report the full error output**. Nothing else will
work until UTP2 builds cleanly.

### Step 3 — confirm the project builds
```bash
cd /home/dusty/Desktop/Isabelle/project && \
  /home/dusty/Desktop/Isabelle/project/Isabelle2025-2/bin/isabelle build -D .
```
This is the **authoritative build command**. Use it and no other.

> **IMPORTANT — Bash tool timeout:** Every `isabelle build` invocation **must** use a
> timeout of at least **1 800 000 ms (30 minutes)** in the Bash tool. The build
> compiles UTP2 and all its dependencies from scratch on a cold cache, which
> routinely takes 5–15 minutes. **Never** call `isabelle build` with a 5-minute
> (300 000 ms) or shorter timeout — the build will be killed mid-run and leave
> the session in a broken state.

---

## 1. The Sorry-First Workflow (ABSOLUTE RULE)

This is the central methodology. Every proof must follow this sequence
without exception.

### The sequence

1. Write the lemma or theorem statement.
2. Insert `sorry` as the entire proof body. No other tactic — not `by blast`,
   not `by simp`, not `done`, not even a single `apply`. Just `sorry`.
3. Build to confirm the statement parses and the file is well-formed.
4. Use `desorry` or `eval_at` with `sledgehammer` to find a proof (see Section 2).
5. Substitute the found proof for `sorry`.
6. Build again to confirm the proof is accepted.
7. If sledgehammer fails, decompose the goal into smaller `have` steps,
   each with its own `sorry`, and repeat from step 4 for each piece.

### Why this rule is absolute

Importing UTP2 brings in thousands of simp rules. A single unconstrained
`by auto` or `by blast` on a UTP goal can run for minutes or hang
indefinitely without any indication of progress. The sorry-first workflow
ensures every tactic is either found by sledgehammer (and therefore known
to terminate) or is a small, explicitly targeted step.

**If you find yourself writing a tactic before running sledgehammer, stop.
Insert `sorry` first, build, then use the tools.**

---

## 2. CLI Tools: How to Use Them

Both tools require `-l` and `-d` flags for this project because
`Angelic_Processes` is a custom session, not a standard HOL session.

### Shorthand (define these as shell variables at the start of a session)
```bash
ISA=/home/dusty/Desktop/Isabelle/project/Isabelle2025-2/bin/isabelle
PROJ=/home/dusty/Desktop/Isabelle/project
THY=$PROJ/Angelic_Processes.thy
```

### `eval_at` — inspect proof state or run a command at a line

**Show the proof state at a line (no command):**
```bash
$ISA eval_at -l Angelic_Processes -d $PROJ $THY LINE_NUMBER
```

**Run sledgehammer at a specific sorry:**
```bash
$ISA eval_at -l Angelic_Processes -d $PROJ $THY LINE_NUMBER 'sledgehammer'
```

**Run sledgehammer with a longer timeout:**
```bash
$ISA eval_at -l Angelic_Processes -d $PROJ $THY LINE_NUMBER \
  'sledgehammer [timeout = 60]'
```

**Search for relevant theorems at a line:**
```bash
$ISA eval_at -l Angelic_Processes -d $PROJ $THY LINE_NUMBER \
  'find_theorems "your_pattern"'
```

**Try a tactic and see the resulting proof state:**
```bash
$ISA eval_at -s -l Angelic_Processes -d $PROJ $THY LINE_NUMBER \
  'apply rel_simp'
```

**Profile timing up to a line (identify slow steps):**
```bash
$ISA eval_at -t -l Angelic_Processes -d $PROJ $THY LINE_NUMBER
```

### `desorry` — bulk sorry elimination

**Replace all sorry's in the theory file (parallel sledgehammer):**
```bash
$ISA desorry -l Angelic_Processes -d $PROJ $THY
```

**Replace sorry's up to a specific line:**
```bash
$ISA desorry -l Angelic_Processes -d $PROJ $THY LINE_NUMBER
```

**Target specific sorry's by line number:**
```bash
$ISA desorry -L 42,105,210 -l Angelic_Processes -d $PROJ $THY
```

**Use a longer timeout per sorry (default is 30s):**
```bash
$ISA desorry -t 60 -l Angelic_Processes -d $PROJ $THY
```

`desorry` automatically saves a backup to `Angelic_Processes.thy.backup`
before modifying the file. To revert:
```bash
cp /home/dusty/Desktop/Isabelle/project/Angelic_Processes.thy.backup \
   /home/dusty/Desktop/Isabelle/project/Angelic_Processes.thy
```

### Typical proof development loop

```
1. Add lemma with sorry  →  isabelle build  (confirm it parses)
2. desorry               →  tries sledgehammer on all sorry's in parallel
3. isabelle build        →  confirm found proofs are accepted
4. If a sorry remains:
     eval_at ... 'sledgehammer [timeout=60]'   (try longer timeout)
     eval_at ... 'find_theorems "..."'         (search for useful lemmas)
     eval_at -s ... 'apply rel_simp'           (inspect state after tactic)
     decompose into have steps with sorry's, then repeat from step 2
```

---

## 3. Build and Sanity Checks

### The authoritative build command
```bash
cd /home/dusty/Desktop/Isabelle/project && \
  /home/dusty/Desktop/Isabelle/project/Isabelle2025-2/bin/isabelle build -D .
```

### When to build
- After adding or changing any definition
- After adding or changing any lemma or theorem statement
- After finishing any proof (or partial proof with sorry)
- After any refactoring of imports or file structure
- After every `desorry` run

### What success means
Isabelle reports no errors. Sorry's are acceptable and expected — they
produce warnings, not errors. The theory must parse and typecheck cleanly.

---

## 4. File and Theory Structure

### Main theory: `Angelic_Processes.thy`
- Imports `UTP2.utp` and nothing else at the top level.
- Structured with `section`, `subsection`, and `text` blocks.
- Do **not** add a "Background" section — UTP2 is the background.
- Informal notation in `main.tex` will need adaptation to UTP's type
  system. Identify the right UTP type for each construct first:
  - Predicates: `'\<alpha> upred`
  - Relations: `'\<alpha> hrel`
  - Designs: `'\<alpha> hrel_des`
  Check Foster's theories before defining anything that might already exist.

### Splitting into auxiliary theories (only if needed)
If `Angelic_Processes.thy` grows unwieldy, split into helper theories
(e.g. `Angelic_Processes_Defs.thy`, `Angelic_Processes_Laws.thy`), but:
- keep `Angelic_Processes` as the single top-level theory,
- ensure it imports everything needed,
- update ROOT so the build command still works,
- update all `desorry` and `eval_at` calls to target the correct `.thy` file.

---

## 5. Proof Engineering Guidelines

### Search UTP's library before proving anything
```bash
grep -r "concept_name" /home/dusty/Desktop/Isabelle/project/UTP-main/
```
UTP2 provides algebraic laws for refinement (`\<sqsubseteq>`), sequential
composition, angelic and demonic choice, and much more. Always check
`utp_pred.thy`, `utp_rel.thy`, and `utp_designs.thy` before writing a
proof from scratch.

### UTP proof tactics (prefer these over raw Isabelle automation)
These tactics understand UTP's type and alphabet structure:

| Tactic | Use for |
|---|---|
| `rel_auto` | Full relational/predicate discharge |
| `rel_simp` | Lighter relational simplification |
| `pred_auto` | Pure predicate goals |
| `pred_simp` | Lighter predicate simplification |
| `subst_tac` | Substitution goals |

Even these can time out on large goals. Always try them via the
sorry-first workflow — `desorry` or `eval_at` with sledgehammer first,
then fall back to manual UTP tactics if sledgehammer cannot find a proof.

### Proof structure
- Split big theorems into named `have` steps and helper lemmas.
- Name every intermediate fact: `have hfoo: "..." by ...`
- Supply named facts to the closing tactic via `using`.
- When UTP tactics fail, use structured proofs (`proof -` / `qed`) and
  apply UTP algebraic laws step by step.

### Simp discipline
UTP's simp sets are already large. Never extend them globally.
- Always use `simp add: specific_rule` not bare `simp`.
- Never use `simp_all`.
- Prefer `simp only: rule1 rule2` when the goal is well understood.

### Naming conventions
- Definitions: `ap_...` prefix throughout
- Lemmas: descriptive names with suffixes `_intro`, `_elim`, `_simp`,
  `_iff` where conventional
- Refinement laws: `_refine` or `_mono` suffixes

---

## 6. Documentation and Change Logging

### In the source file
Use `text ‹ … ›` before major definitions and theorems explaining:
- the informal counterpart in `main.tex` (cite section or page),
- which UTP layer this construct lives in,
- key dependencies on Foster's theories.

### CHANGES.md
Maintain `/home/dusty/Desktop/Isabelle/project/CHANGES.md` with:
- dated buildable milestones,
- notable new definitions and lemmas,
- sorry's removed or introduced and why.

### Backups
After a meaningful block of work, save a numbered backup:
```bash
cp /home/dusty/Desktop/Isabelle/project/Angelic_Processes.thy \
   /home/dusty/Desktop/Isabelle/project/bck0001.thy
```
Validate each backup builds before moving on. Increment the number each time.

---

## 7. Timeout Discipline

### High-risk tactics — never use one-shot in `by (...)`

* `simp`, `simp_all`
* `auto`, `force`, `fastforce`
* `blast`
* `meson`, `metis`, `smt`
* `rel_auto`, `pred_auto` (on large or deeply nested UTP goals)

### Always split automation into visible steps

Instead of:
```isabelle
by (auto simp: A B intro: C)
```
Write:
```isabelle
apply (simp add: A B)
apply (intro C)
apply blast
done
```

For UTP goals:
```isabelle
apply rel_simp
apply (simp add: specific_utp_law)
apply pred_auto
done
```

### If a build times out

1. Replace the offending tactic with `sorry`.
2. Rebuild to confirm the file is green.
3. Use `eval_at` to inspect the goal state at that line.
4. Reintroduce the proof in smaller `have` steps, each with `sorry`.
5. Run `desorry` to fill them in.
6. If still stuck, fall back manually:
   - `rel_auto` → `rel_simp` + explicit UTP law
   - `auto` → `simp` + `blast`
   - `blast` → structured `intro` / `elim`
   - `metis` → explicit lemma chain

### The golden rule

If a tactic touches UTP alphabet expressions, lens bindings, large
refinement chains, or many UTP rewrite rules simultaneously — assume
it will explode. Proceed one step at a time.

---

## 8. Quality Bar and Progression

### The project must always build
Every checkpoint must pass:
```bash
cd /home/dusty/Desktop/Isabelle/project && \
  /home/dusty/Desktop/Isabelle/project/Isabelle2025-2/bin/isabelle build -D .
```

### Progression targets
- Reduce sorry count steadily; never increase it without a plan to
  discharge the new sorry's promptly.
- Prioritize main process-algebraic theorems first, then corollaries
  and derived laws.
- Do not skip easy sorry's if they block downstream results.

### When stuck
Do **not** stall:
- Isolate the hard part into a named helper lemma with `sorry`.
- Add a `text` note explaining the intended proof strategy and which
  UTP laws are likely relevant.
- Continue downstream development, then return to discharge the `sorry`.
