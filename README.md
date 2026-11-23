# Arakelov-Filtered Automorphic Period Towers: $\mathbb{Q}$-GRH Monograph and ERH Extension

This repository hosts two companion mathematical works:

1. **[`main.pdf`](main.pdf)** (178 pages) & **[`chapters/appB_bibliography_and_lean_map.tex`](chapters/appB_bibliography_and_lean_map.tex)**  
   A human-readable structuralist monograph and Lean~4.33.1 archive concordance for the Generalized Riemann Hypothesis (GRH) for Dirichlet $L$-functions over $\mathbb{Q}$.

2. **[`erh_extension/erh_paper.pdf`](erh_extension/erh_paper.pdf)** (21 pages, `amsart`)  
   **Prismatic $\mathrm{LiftK}$, Brauer--Artin Iwasawa Descent, Automorphic Selmer Obstructions, and the Extended Riemann Hypothesis over Totally Real and CM Fields** (Waves~1--17 synthesis, rigorously calibrated into `[PROVED]`, `[PROVED-MOD-EXPLICIT-LEMMA]`, `[CONDITIONAL]`, and `[OPEN-OBSTRUCTION]` results):
   - **LaTeX Source**: [`erh_extension/erh_paper.tex`](erh_extension/erh_paper.tex) and [`erh_extension/sections/`](erh_extension/sections) (compile with `cd erh_extension && tectonic erh_paper.tex` or `make pdf`).
   - **Lean~4.33.1 Blueprints** ([`erh_extension/lean_erh_blueprint/`](erh_extension/lean_erh_blueprint)): 14 modules (5,762 lines), statically verified for syntax, interface consistency, and zero `sorry` (`lake build` pending).
   - **Verification Scripts** ([`erh_extension/scripts/`](erh_extension/scripts)): 109 Python/SymPy scripts covering finite-instance checks, 40-digit interval arithmetic, Higham floating-point error bounds, and adversarial audit suites (Waves~8--17).

## Highlights of `erh_extension/`

- **Unconditional Closure of Regime~B Prismatic $\mathrm{LiftK}$ (Item~8)**: Universal $H^2_{\mathrm{syn}}$ annihilation across all primes $\ell \ge 2$ and all wild non-abelian $K/\mathbb{Q}_\ell$, Nygaard-free Frobenius-pullback complex $R\Gamma_{\mathrm{BK}}^*$, exact refutation of pure 2D lattice algebra `K02-Q1` ($c_{\mathrm{opt}}(d) = \lfloor d/2 \rfloor$ via Matlis quadruple duality), and prismatic PD horizontal-section theorem yielding $\exp_\ell(Q_1(T_0)_{\mathrm{tors}}) \le N_{Q_1}(K, M) = O_{K_1}(sM)$ independent of rank $d$. Zero drift through `ch23`--B9.
- **Non-Abelian $\mu_2 = 0$, Brauer--Artin Descent, and $S_3$ Arithmetic Statistics**: Elementary $2$-adic Kronecker reflection, $100\%$ classification of $G' \le O_2(G)$, Brauer--Artin analytic $\mu_\ell$-descent bypassing the $\mathbb{F}_2[A_5]$ module obstruction, unconditional zero-GRH certification of $A_5(10931^2)$, $A_5(11699^2)$, and $S_5(7^3\cdot 11^3\cdot 41^2)$ plus infinite pure Regime-A $P_2 \times A_5$ and $C_2^{4m} \rtimes A_5$ towers, zero-preprint $T_1 \gg X^{5/6}$ and $N_{\ge 2} \gg X^{0.5548}$ for $S_3$ cubic fields, and $\ge 0.03940\,X^{5/6}$ tame $S_3$ fields with $\mu_2 = \lambda_2 = 0$ (modulo Shankar--Tsimerman 2025 preprints).
- **Automorphic Selmer & Reductive Architecture Theorems**: Real-quadratic Count~I across all $K_0 = \mathbb{Q}(\sqrt{D})$, definite-quaternion Eisenstein analytic $\mu_{\mathrm{an}}^{\mathrm{opt}} = 0$ in degree $d_0 \ge 3$, $\zeta_\ell$-admissible prime Catch-22, Bott-periodicity non-transfer to $\mathrm{GSpin}(5,2)$, and the Four-Pillar Reductive Group No-Go Theorem.
- **Unified Real-Quadratic $D_4/Q_8$ ERH Reduction & $\Delta$-Nontrivial Control**: Exact iff Regime~A/B criterion, reduction of all totally real and CM $D_4/Q_8$ fields over arbitrary $K_0 = \mathbb{Q}(\sqrt{D})$ to explicit interfaces (`Theorem U-D4Q8-ERH`), and universal $\Delta$-nontrivial control proving fixed-twist vanishing of `b1p` and `b1`-odd for $100\%$ of large primes.
