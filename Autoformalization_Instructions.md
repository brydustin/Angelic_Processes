# Autoformalization Instructions: Angelic Processes

This project formalizes Pedro Ribeiro's dissertation, *Angelic Processes*, on top of
the local Isabelle/UTP sessions in this directory.

The current entry point is:

- Theory: `Angelic_Processes.thy`
- Session: `Angelic_Processes`
- Isabelle: `/home/dusty/Desktop/Isabelle/project/Isabelle2025-2/bin/isabelle`

## Isabelle Commands

The normal project build command should eventually be:

```bash
/home/dusty/Desktop/Isabelle/project/Isabelle2025-2/bin/isabelle build \
  -d /home/dusty/Desktop/Isabelle/project \
  -l Angelic_Processes
```

At present, the default Isabelle user setup loads AFP globally. That collides with
the local `Z_Toolkit-main` session because both define a session named `Z_Toolkit`.
Use an isolated Isabelle identifier for this project:

```bash
cd /home/dusty/Desktop/Isabelle/project

ISABELLE_IDENTIFIER=IsabelleAPRoadmap \
/home/dusty/Desktop/Isabelle/project/Isabelle2025-2/bin/isabelle build \
  -d /home/dusty/Desktop/Isabelle/project \
  -d /home/dusty/Desktop/Isabelle/project/Abstract_Prog_Syntax-main \
  -d /home/dusty/Desktop/Isabelle/project/Z_Toolkit-main \
  -d /home/dusty/Desktop/Isabelle/project/Shallow-Expressions-main \
  -d /home/dusty/Desktop/Isabelle/project/Shallow-Expressions-main/Z \
  -d /home/dusty/Desktop/Isabelle/project/Optics-main \
  -d /home/dusty/Desktop/Isabelle/project/UTP-main \
  Angelic_Processes
```

Open the theory in jEdit with:

```bash
cd /home/dusty/Desktop/Isabelle/project

ISABELLE_IDENTIFIER=IsabelleAPRoadmap \
/home/dusty/Desktop/Isabelle/project/Isabelle2025-2/bin/isabelle jedit \
  -d /home/dusty/Desktop/Isabelle/project \
  -d /home/dusty/Desktop/Isabelle/project/Abstract_Prog_Syntax-main \
  -d /home/dusty/Desktop/Isabelle/project/Z_Toolkit-main \
  -d /home/dusty/Desktop/Isabelle/project/Shallow-Expressions-main \
  -d /home/dusty/Desktop/Isabelle/project/Shallow-Expressions-main/Z \
  -d /home/dusty/Desktop/Isabelle/project/Optics-main \
  -d /home/dusty/Desktop/Isabelle/project/UTP-main \
  -l Angelic_Processes \
  /home/dusty/Desktop/Isabelle/project/Angelic_Processes.thy
```

## Roadmap Discipline

Do not start by proving large theorems. The dissertation appendices are highly
regular, and the proof strategy should exploit that regularity.

For each layer:

1. Freeze definitions and names.
2. State all lemmas from the relevant thesis section as Isabelle lemmas.
3. Leave each new lemma as `sorry`.
4. Split hard goals into small intermediate `have` statements only when beginning
   a proof pass.
5. Use `eval_at` or jEdit proof-state inspection before trying automation.
6. Use Sledgehammer or `desorry` on small residual goals, not on large theorem
   statements.

## Layer Order

The intended dependency order is:

1. Extended binary multirelations: `BMH0`, `BMH1`, `BMH2`, `BMH3`, fixed-point
   forms `bmh0`, `bmh1`, `bmh2`, `bmh3`, operators, and the `bm2bmb`/`bmb2bm`
   isomorphism.
2. Angelic designs: `PBMH`, `A0`, `A1`, `A`, `A2`, angelic/demonic choice,
   sequential composition, `d2bmb`/`bmb2d`, `d2ac`/`ac2p`, and `d2pbmh`/`pbmh2d`.
3. Reactive angelic designs: `RA1`, `RA2`, `RA3`, `RA`, `CSPA1`, `CSPA2`, `RAD`,
   `NDRAD`, CSP linking, and RAD operator laws.
4. Angelic processes: `IIAP`, `RA3AP`, `AP`, `NDAP`, RAD/AP linking, AP operator
   laws, and the headline prefix/divergence theorem.

## Proof Batches

Recommended first proof batches:

1. Set-theoretic BMH fixed-point lemmas:
   `ap_BMH0_fixed_point_iff`, `ap_BMH1_fixed_point_iff`,
   `ap_BMH2_fixed_point_iff`, `ap_BMH3_fixed_point_iff`.
2. Idempotence lemmas:
   `ap_bmh0_idem`, `ap_bmh1_idem`, `ap_bmh2_idem`, `ap_bmh3_idem`,
   `ap_PBMH_idem`, `ap_A0_idem`, `ap_A1_idem`.
3. Closure lemmas for conjunction/disjunction operators.
4. Linking theorems only after their endpoint closure properties are available.

## Source Mapping

Use these dissertation sections as the proof oracle:

- Chapter 3 and Appendix B: extended binary multirelations.
- Chapter 4 and Appendices C, E, F: angelic designs, PBMH, and sequential
  composition.
- Chapter 5 and Appendix G: reactive angelic designs.
- Chapter 6 and Appendix H: angelic processes and the headline divergence laws.

The fellowship presentation and `fellowship_strategy.md` set the intended milestone
order. The Isabelle file should track those milestones rather than trying to
mechanize the thesis linearly.

## Current Status

`Angelic_Processes.thy` currently builds with `sorry` placeholders under the
isolated `IsabelleAPRoadmap` identifier. It is a typed roadmap, not a completed
formalization.
