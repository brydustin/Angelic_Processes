# Angelic Processes in Isabelle/UTP — 10-week Fellowship Strategy

**Candidate approach:** autoformalisation on top of the existing Isabelle/UTP session, using the same tool-assisted pipeline already validated on the Paulsen quantum-computing formalisation.

---

## 1. Methodology: autoformalisation, not hand-transcription

The thesis appendices (B, C, F, G, H — ~650 pp) are an unusually regular body of proof: hundreds of near-template lemmas about healthiness-condition commutation, idempotence, closure under operators, and Galois-connection endpoints. That regularity is exactly what the autoformalisation pipeline is designed to exploit.

The pipeline has three layers, in the order they are applied to every lemma:

1. **LLM-assisted Isar skeleton generation.** The thesis statement is translated to an Isabelle `lemma`/`theorem` with a skeletal Isar proof that decomposes the obligation into sub-`have` lines mirroring the thesis proof structure. Definitions from the paper/thesis are translated first so names line up.
2. **`isabelle eval_at` for proof-state introspection.** Before committing any proof step, the current subgoal state is read directly from the running session (`eval_at THY LINE`) — the same `sledgehammer`/`find_theorems`/`thm` commands available inside jEdit, but callable from the agent loop. No "write proof blind, hope it builds."
3. **`isabelle desorry` for batch residual closure.** Remaining `sorry` placeholders are closed in parallel by `desorry -L <lines>`, which runs sledgehammer on each and overwrites the file with the found `by ...` proofs.

**Rule (carried over from the QC project):** decompose into small `have` lines first, invoke `desorry`/`sledgehammer` second. Sledgehammer fails on multi-fact goals but succeeds reliably on the sub-goals left after hand decomposition. This is the single most important workflow habit; it is what made the QC formalisation tractable.

**Why this matters for a 10-week budget:** hand-transcription of 650 pages of appendix proofs is not feasible in 10 weeks. The autoformalisation pipeline turns the job into *reviewing and guiding* machine-generated proofs, with human effort concentrated on the theorems that actually require mathematical judgement — the Galois connections between layers.

---

## 2. Reading order: paper first, thesis as proof oracle

- **Week 0 (pre-fellowship):** read the paper (Ribeiro & Cavalcanti, TCS 2019, 45 pp) end-to-end. This is the theory architecture — angelic designs → reactive angelic designs → angelic processes, linked by Galois connections.
- **During the fellowship:** thesis §2 for UTP/background refresh; appendices B/C/G/H opened *per lemma* as the proof oracle, not read linearly.

The thesis body chapters 3–6 are a slightly more verbose restatement of paper §§4–7. The appendices are the only thing the paper doesn't contain, and they are exactly what autoformalisation consumes.

---

## 3. Week 1 mapping note (deliverable for the interview)

| Paper § | Definition / Theorem            | Planned Isabelle name          | Thesis proof source |
|---------|---------------------------------|--------------------------------|---------------------|
| §3      | `fd2r` (failures-divergences → relation)   | `fd2r_def`                | Def 1, pp. 21–22 |
| §4.1    | `BMH0`, `BMH1`, `BMH2`, `BMH3`  | `BMH0`–`BMH3`                  | App B.1–B.2 |
| §4.1    | Fixed-point forms `bmh₀…bmh₃`   | `bmh0`–`bmh3`                  | App B.2.1–B.2.4 |
| §4.2    | Angelic / demonic / `;` on BMs  | `bm_angelic`, `bm_demonic`, `bm_seq` | App B.3 |
| §4.3    | `bm2bmb` / `bmb2bm` iso         | `bm_bmb_iso`                   | App B.4 |
| §5.1    | Alphabet + `A0`–`A2`            | `A0`–`A2`                      | App C.1 |
| §5.2    | `d2bmb` / `bmb2d` iso           | `d2bmb_bmb2d_iso`              | App C.2 |
| §5.3    | Refinement via extreme points   | `ad_refine_extreme`            | App C.3 |
| §5.4    | Operators on ADs                | `ad_seq`, `ad_demonic`, `ad_angelic` | App C.4 |
| §5.5    | `d2ac` / `ac2p` Galois          | `d2ac_ac2p_galois`             | App C.5.4 |
| §5.6    | `d2pbmh` / `pbmh2d` iso         | `pbmh_iso`                     | App C.6 |
| §6.2    | `RA1`, `RA2`, `RA3`, `RA`       | `RA1`–`RA`                     | App G.1–G.4 |
| §6.3    | CSP-angelic subtheory `CSPA1`   | `CSPA1`                        | App G.5 |
| §6.4    | Non-divergent RAD `NDRAD`        | `ND_RAD`                       | App G.6 |
| §6.5    | `ac2p`/`p2ac` Galois to CSP     | `rad_csp_galois`               | App G.7 |
| §6.6    | Operator laws (angelic, ⊓, Chaos, Choice, Stop, Skip, `;`, prefix, □) | `rad_*_law` | App G.8 |
| §7.1    | `RA3_AP`, `AP`, `ND_APₙ`         | `RA3_AP`, `AP`, `ND_AP`        | App H.1 |
| §7.2    | RAD ↔ AP Galois                 | `rad_ap_galois`                | App H.2 |
| §7.3    | `a → Skip ⊓ b → Chaos = a → Skip` | `angelic_avoids_divergence_thm` | App H.3 |
| §7.3    | Operator laws on APs            | `ap_*_law`                     | App H.3 |

Already in Isabelle/UTP (AFP): all of thesis App A (Relations, Designs, Reactive, CSP). **Not re-formalised.**

---

## 4. 10-week timeline

| Wk | Focus | Milestone | Autoformalisation stage |
|----|-------|-----------|-------------------------|
| 1 | Paper re-read; thesis §1–2; AFP `UTP` audit; `ROOT` + CI; name-mapping note frozen | The table above as source-of-truth | Setup `eval_at`/`desorry` against the Angelic_UTP session |
| 2 | Ext. Binary Multirelations (App B) — warm-up layer | `bm2bmb`/`bmb2bm` iso mechanised | Full pipeline: skeletons → `eval_at` guidance → `desorry` batch close |
| 3–4 | Angelic Designs (App C) — largest proof surface | `d2bmb`/`bmb2d` iso + `d2ac`/`ac2p` Galois mechanised | Decompose before `desorry`; reusable tactics harvested |
| 5–6 | Reactive Angelic Designs (App G) | RAD ↔ CSP Galois mechanised | Reuse Isabelle/UTP reactive machinery; no redefinitions |
| 7–8 | Angelic Processes (App H) | `a → Skip ⊓ b → Chaos = a → Skip` mechanised — the headline theorem | — |
| 9 | Examples + algebraic law library | User-facing API of the session | Law bank auto-harvested from App G.8 / H.3 via batched `desorry` |
| 10 | Hardening, naming, AFP-style docs; PDF report mapping every paper theorem to Isabelle name:line | Stretch: AFP submission | — |

**Go/no-go checkpoints:** end of Wk 2 (pipeline working end-to-end on a real layer), end of Wk 4 (first Galois connection closed), end of Wk 8 (headline theorem closed). Miss any of these → scope down Wk 9.

---

## 5. Risk register

- **App proofs are 10+ years old and hand-written.** Typos and missing lemmas will surface. Mitigation: fallback to stating a result as an axiom with a `TODO` tag, flag in the report, move on. No single lemma consumes more than a day.
- **`desorry` timeouts on hard closures.** Mitigation: the QC-project feedback rule — decompose first, invoke tools on residuals. Budget assumes this is the default workflow.
- **Name collisions with existing Isabelle/UTP.** Mitigation: namespace everything under `Angelic_UTP.*`; resolve in Wk 1 during the AFP audit.
- **LLM-generated skeletons drift from thesis notation.** Mitigation: definitions translated and frozen first (Wk 1), proofs generated against the frozen names only.

---

## 6. What to say in the interview (one-sentence versions)

- *"Paper first, thesis as proof oracle — the paper is the map, the appendices are the terrain."*
- *"Same autoformalisation pipeline we validated on the Paulsen QC project: LLM-drafted Isar skeletons, `eval_at` for live proof-state, `desorry` for batched sledgehammer closure, hand-decomposition before any tool invocation."*
- *"Four theory files, three Galois-connection milestones, one headline theorem — `a → Skip ⊓ b → Chaos = a → Skip` — mechanised by week 8."*
- *"Reuse, don't reinvent: thesis Appendix A is already in AFP `UTP`; I don't re-formalise it."*
