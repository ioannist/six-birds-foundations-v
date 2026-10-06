# External anchors

Every citation in `paper/references.bib` that is not a Six Birds corpus paper, with the metadata verified on 2026-09-02, the verification route, and the result or sentence it supports. "Recovered result" means the manuscript recovers a mathematical statement from the source (label RECOVERED STANDARD); "recognition" means the source is named as a conceptual neighbour or empirical motivation only and no result is taken from it. Corpus (Six Birds) entries are listed in §2 with their canonical-text status.

## 1. External entries

| Key | Verified metadata | Route | Supports | Role |
|---|---|---|---|---|
| `BoydVandenberghe2004` | Boyd, S.; Vandenberghe, L. *Convex Optimization*. Cambridge University Press, 2004. DOI 10.1017/CBO9780511804441. §5.4.4 "Price or tax interpretation" pp. 240–241 (shadow prices); §5.5.2 "Complementary slackness" pp. 242–243, eq. (5.48); §5.5.3 "KKT optimality conditions" pp. 243–244, eq. (5.49); §5.6.3 "Local sensitivity analysis" p. 251 | Crossref record (title, authors, publisher, year); sections and pages read from the book's table of contents and text (PDF from the authors' site) | §2 shadow-price identity; E6 (Thm 6.1) KKT and slack; E8 (Thm 6.3) sensitivity identity; App. C `E6_SlackCollapse` | **recovered result** (RECOVERED STANDARD), in weaker Lean form |
| `Sims2003` | Sims, C. A. "Implications of rational inattention." *Journal of Monetary Economics* 50(3):665–690, 2003. DOI 10.1016/S0304-3932(03)00029-1 | Crossref | E6 instance sentence | recognition |
| `Lucas1976` | Lucas, R. E., Jr. "Econometric policy evaluation: A critique." *Carnegie-Rochester Conference Series on Public Policy* 1:19–46, 1976. DOI 10.1016/S0167-2231(76)80003-6 | Crossref | E11 instance sentence | recognition |
| `Coase1937` | Coase, R. H. "The Nature of the Firm." *Economica* 4(16):386–405, 1937. DOI 10.1111/j.1468-0335.1937.tb00002.x | Crossref | E12 instance sentence | recognition |
| `MaturanaVarela1980` | Maturana, H. R.; Varela, F. J. *Autopoiesis and Cognition: The Realization of the Living*. Boston Studies in the Philosophy of Science 42, D. Reidel (Springer Netherlands), Dordrecht, 1980. DOI 10.1007/978-94-009-8947-4 | Crossref | §1 and E1 instance sentences | recognition |
| `Rosen1991` | Rosen, R. *Life Itself: A Comprehensive Inquiry into the Nature, Origin, and Fabrication of Life*. Columbia University Press, New York, 1991 (xix + 284 pp.; ISBN 0-231-07564-2). No DOI. | Publisher page (cup.columbia.edu) and the *International Journal of General Systems* review record (DOI 10.1080/03081079308945090) | §1 | recognition |
| `MorenoMossio2015` | Moreno, A.; Mossio, M. *Biological Autonomy: A Philosophical and Theoretical Enquiry*. Springer Netherlands, Dordrecht, 2015. DOI 10.1007/978-94-017-9837-2 | Crossref | §1, E1, E3 instance sentences | recognition |
| `MonteilMossio2015` | Montévil, M.; Mossio, M. "Biological organisation as closure of constraints." *Journal of Theoretical Biology* 372:179–191, 2015. DOI 10.1016/j.jtbi.2015.02.029 | Crossref | §1, E3 instance sentences | recognition |
| `Ashby1956` | Ashby, W. R. *An Introduction to Cybernetics*. Chapman and Hall, London, 1956 (ix + 295 pp.). No DOI. | Contemporary review records (Journal of Mental Science; British Journal for the Philosophy of Science 9(34), DOI 10.1093/bjps/IX.34.168) | E2 instance sentence | recognition |
| `ConantAshby1970` | Conant, R. C.; Ashby, W. R. "Every good regulator of a system must be a model of that system." *International Journal of Systems Science* 1(2):89–97, 1970. DOI 10.1080/00207727008920220 | Crossref | E2 instance sentence | recognition |
| `SterlingEyer1988` | Sterling, P.; Eyer, J. "Allostasis: A new paradigm to explain arousal pathology." In S. Fisher and J. Reason (eds.), *Handbook of Life Stress, Cognition and Health*, Wiley, New York, 1988, pp. 629–649. No DOI. | PsycNET record 1988-98352-034 and multiple bibliographic listings | E8 instance sentence | recognition |
| `PezzuloLevin2015` | Pezzulo, G.; Levin, M. "Re-membering the body: applications of computational neuroscience to the top-down control of regeneration of limbs and other complex organs." *Integrative Biology* 7(12):1487–1517, 2015. DOI 10.1039/C5IB00221D | Crossref | E11 instance sentence; §11 HoloLife-1 motivation | recognition |
| `GodfreySmith2009` | Godfrey-Smith, P. *Darwinian Populations and Natural Selection*. Oxford University Press, Oxford, 2009. DOI 10.1093/acprof:osobl/9780199552047.001.0001 | Crossref | E12 instance sentence | recognition |
| `Clarke2010` | Clarke, E. "The Problem of Biological Individuality." *Biological Theory* 5(4):312–325, 2010. DOI 10.1162/BIOT_a_00068 | Crossref | E12 instance sentence | recognition |
| `NeteaEtAl2016` | Netea, M. G.; Joosten, L. A. B.; Latz, E.; Mills, K. H. G.; Natoli, G.; Stunnenberg, H. G.; O'Neill, L. A. J.; Xavier, R. J. "Trained immunity: A program of innate immune memory in health and disease." *Science* 352(6284):aaf1098, 2016. DOI 10.1126/science.aaf1098 | Crossref | E16 instance sentence | recognition |
| `NaderSchafeLeDoux2000` | Nader, K.; Schafe, G. E.; LeDoux, J. E. "Fear memories require protein synthesis in the amygdala for reconsolidation after retrieval." *Nature* 406(6797):722–726, 2000. DOI 10.1038/35021052 | Crossref | E14 instance sentence | recognition |
| `Dudai2004` | Dudai, Y. "The Neurobiology of Consolidations, Or, How Stable Is the Engram?" *Annual Review of Psychology* 55:51–86, 2004. DOI 10.1146/annurev.psych.55.090902.142050 | Crossref | E14 instance sentence | recognition |
| `WalkerStickgold2006` | Walker, M. P.; Stickgold, R. "Sleep, Memory, and Plasticity." *Annual Review of Psychology* 57:139–166, 2006. DOI 10.1146/annurev.psych.56.091103.070307 | Crossref (the DOI string carries volume 56 in its suffix but resolves to the volume-57 article) | E15 instance sentence | recognition |

All eighteen external entries verified; none removed. Bibliography corrections applied in Phase 3 to external entries: the `Nature` entry gains its issue number 6797; nothing else changed.

## 2. Corpus entries

| Key | Verified metadata | Canonical text | Use |
|---|---|---|---|
| `Tsiokos2026FoundI` | arXiv:2602.00134 [cs.LO], submitted 2026-01-28; DOI 10.48550/arXiv.2602.00134 | in checkout | Def. 2.1; E1 (Thm 6); primitive roles |
| `Tsiokos2026FoundII` | Zenodo 10.5281/zenodo.19672278, preprint, 2026-04-20 (Zenodo API); DOI added to bib | in checkout | §1 meta-limit (§11.3); primitive roles (§2) |
| `Tsiokos2026FoundIII` | no DOI in bib and none printed in the checkout text | in checkout; Lean vendored | Thms 8, 19, 24, 25; §4.7; §11; NC-TD |
| `Tsiokos2026FoundIV` | Zenodo 10.5281/zenodo.20713187, preprint, published 2026-06-17 (Zenodo API) | in checkout | F-laws as listed |
| `Tsiokos2026FoundVI` | manuscript, no identifier | **not available** | forward pointer only |
| `Tsiokos2026Adequacy` | Zenodo 10.5281/zenodo.20713713, preprint, 2026-06-17; DOI added | in checkout; Lean vendored | Defs 4.2, 10.1; Thm 8.2; Cor. 8.3; Thm 10.2 |
| `Tsiokos2026Currency` | Zenodo 10.5281/zenodo.18926771, preprint, 2026-03-09, title "To Spend a Stone with Six Birds: Currency–Constraint Duality and Shadow Prices Across Closure Layers" (en dash, `--` in the bib); DOI added and bib title corrected (was "Currency, Constraint Duality, and") | in checkout | §2.3, §3.2, §3.5, §5.2, §5.4, §6.1 |
| `Tsiokos2026NeedleKiller` | Zenodo 10.5281/zenodo.20713688, preprint, 2026-06-17; DOI added; title capitalization "Emergence IS the Needle Killer" restored in the bib | in checkout | §9 open problem |
| `Tsiokos2026Hiddenness` | Zenodo 10.5281/zenodo.20713577, preprint, 2026-06-17; DOI added | in checkout | Def. 5.1 |
| `Tsiokos2026Holonomy` | no DOI in bib and none printed in the checkout text; SHA256 of checkout text = review v45 corrected version | in checkout; Lean vendored | Defs 2.1–2.4; Thm 3.6 |
| `Tsiokos2026Agents` | Zenodo 10.5281/zenodo.18439737, preprint, 2026-01-31; DOI added | in checkout | §1.3, §3.5, §5.2 |
| `Tsiokos2026Institutions` | Zenodo 10.5281/zenodo.20713293, preprint, 2026-06-17; DOI added | in checkout | Props 6.2, 6.3, 6.5; §1; §10 |
| `Tsiokos2026Reflexive` | no DOI in bib and none printed in the checkout text | in checkout | §9.3 |
| `Tsiokos2026Life` | bib corrected to the preprint record Zenodo 10.5281/zenodo.18420406 ("To Wake a Stone with Six Birds: A Life is A Theory", 2026-01-29; concept DOI 10.5281/zenodo.18394535); the bib's previous DOI 10.5281/zenodo.18454211 is a *software* record of the same project | **not in checkout**; sibling repository consulted read-only | §11 transcriptions; §13, §14 nonclaims |
| `Tsiokos2026AOR`, `Tsiokos2026Language`, `Tsiokos2026StrictTests` | — | in checkout | **uncited**; removed from the bibliography in Phase 3 |

The seven corpus DOIs added in Phase 3 were taken from the papers' own front matter in the checkout and each resolved through the Zenodo API on 2026-09-02 to a preprint record with the matching title and author. Foundations III, the Holonomy paper, and Reflexive SBT print no identifier in their checkout text; they remain title-only entries.
