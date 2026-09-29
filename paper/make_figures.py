#!/usr/bin/env python3
"""Figures and data tables for the paper, generated from the certified logs.

Everything here is derived from the outputs of the certified runs; nothing is recomputed from scratch.

Reads (paths relative to this file):
  m = 14,501 (Theorem 1.1):
    ../certificate-14501/output/dump_14501.txt.gz   certified per-prime costs; columns: k p which cost M1
                                                    (all p <= 2e5, and every 500th prime by index beyond)
    ../certificate-14501/output/cert_14501.txt      certified totals (eta_up, blocks A/B/C, T_up, f_up, crit_lo, k)
    ../certificate-14501/schedule/sched_14501.json  the 103 knots of the delta schedule
  m = 16,000 (Theorem 1.3, the first formalization):
    ../logs/dump16k.txt     certified per-prime costs for p <= 2e5; columns: k p which cost M1 M2
    ../logs/verbose16k.txt  the certified run with verbose = 1 (running total at sampled p > 2e5)
    ../logs/cert16k.txt     certified totals

Writes:
  fig/cumulative_loss.pdf    Figure 1: running totals of the certified per-prime bounds
  fig/schedule_gain.pdf      Figure 2: the two delta schedules, and the gain over the BBMST moment bounds
  gen/table_budget.tex       the budget of both certificates by prime ranges (main text)
  gen/table_budget_main.tex  the budget of the m = 14,501 certificate by finer ranges (appendix)
  gen/table_budget_fine.tex  the budget of the m = 16,000 certificate between consecutive knots (appendix)
  gen/table_knots_main.tex   the knots of the m = 14,501 schedule (appendix)
  gen/derived.tex            macros for derived statistics quoted in the text

Usage:  python3 make_figures.py      (needs numpy and matplotlib; runs in a few seconds, one core)

Conventions.  Sums of certified costs are exact decimal sums of the printed doubles, rounded UP in the sixth
decimal (they are upper bounds).  The "BBMST-type" bound at p is min(E[U_p], E[U_p^2]/(4 d (1 - d))) with
d = min(delta_p, 1/2), computed from the certified columns M1 = E[U_p(s)] and M2 = E[U_p(s)^2] of the m = 16,000
dump; it is shown for comparison only.
"""
import gzip
import json
import math
import os
import re

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "1")  # one core is plenty
from decimal import Decimal, ROUND_CEILING, ROUND_HALF_UP

import numpy as np
import matplotlib

matplotlib.use("pdf")
import matplotlib.pyplot as plt  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, ".."))
C145 = os.path.join(ROOT, "certificate-14501")
DUMP145 = os.path.join(C145, "output", "dump_14501.txt.gz")
CERT145 = os.path.join(C145, "output", "cert_14501.txt")
SCHED145 = os.path.join(C145, "schedule", "sched_14501.json")
DUMP16 = os.path.join(ROOT, "logs", "dump16k.txt")
VERB16 = os.path.join(ROOT, "logs", "verbose16k.txt")
CERT16 = os.path.join(ROOT, "logs", "cert16k.txt")
FIG = os.path.join(HERE, "fig")
GEN = os.path.join(HERE, "gen")
os.makedirs(FIG, exist_ok=True)
os.makedirs(GEN, exist_ok=True)

PX = 200000          # both dumps list every prime up to 2e5

# ----------------------------------------------------------------------------------------------
# The two schedules (exactly as the checkers' delta_of_rn: double arithmetic, libm log)
# ----------------------------------------------------------------------------------------------
KNOTS16 = [(50, 0.07), (80, 0.1612), (130, 0.2191), (220, 0.2679), (400, 0.3198), (800, 0.345),
           (2000, 0.3762), (8000, 0.4031), (50000, 0.4092)]        # the m = 16,000 run (README, Appendix D)
PD16, PSB16, DSB16 = 50, 31, 0.05
KNOTS145 = [(int(a), float(b)) for a, b in json.load(open(SCHED145))["knots"]]
PD145, PSB145, DSB145 = 17, 0, 0.0                                   # run_certificate.sh: PD=17 PSB=0 DSB=0


def delta_of(p, knots, pd, psb, dsb):
    if p < pd:
        return dsb if (psb > 0 and p >= psb) else 0.0
    lp = math.log(p)
    if lp <= math.log(knots[0][0]):
        return knots[0][1]
    if lp >= math.log(knots[-1][0]):
        return knots[-1][1]
    for (p0, d0), (p1, d1) in zip(knots, knots[1:]):
        if lp <= math.log(p1):
            u = (lp - math.log(p0)) / (math.log(p1) - math.log(p0))
            return d0 * (1 - u) + d1 * u
    return knots[-1][1]


def d16(p):
    return delta_of(p, KNOTS16, PD16, PSB16, DSB16)


def d145(p):
    return delta_of(p, KNOTS145, PD145, PSB145, DSB145)


# ----------------------------------------------------------------------------------------------
# Data
# ----------------------------------------------------------------------------------------------
rows16 = []
for line in open(DUMP16):
    k, p, which, cost, m1, m2 = line.split()
    rows16.append((int(p), int(which), Decimal(cost), float(m1), float(m2)))
P16 = np.array([r[0] for r in rows16], dtype=float)
COST16 = np.array([float(r[2]) for r in rows16])
M1_16 = np.array([r[3] for r in rows16])
M2_16 = np.array([r[4] for r in rows16])
DEL16 = np.array([d16(int(p)) for p in P16])

rows145, samp145 = [], []          # (p, which, cost, M1) for p <= 2e5; sampled (k, p, cost) beyond
with gzip.open(DUMP145, "rt") as f:
    for line in f:
        k, p, which, cost, m1 = line.split()
        if int(p) <= PX:
            rows145.append((int(p), int(which), Decimal(cost), Decimal(m1)))
        else:
            samp145.append((int(k), int(p), float(cost)))
P145 = np.array([r[0] for r in rows145], dtype=float)
COST145 = np.array([float(r[2]) for r in rows145])


def bbmst_bound(m1, m2, d):
    if d <= 0:
        return m1
    dd = min(d, 0.5)
    return min(m1, m2 / (4 * dd * (1 - dd)))


BB16 = np.array([bbmst_bound(a, b, d) for a, b, d in zip(M1_16, M2_16, DEL16)])


def parse_cert(path):
    txt = open(path).read()

    def get(key):
        return re.search(key + r"=([0-9.e+-]+)", txt).group(1)
    return {"eta": get("eta_up"), "A": get(r"\(A"), "B": get("B"), "C": get("C"), "k": int(get("k"))}


cert16 = parse_cert(CERT16)
cert145 = parse_cert(CERT145)

# running totals for p > 2e5 printed by the verbose m = 16,000 run (every 20,000th prime)
vp, ve = [], []
for line in open(VERB16):
    mm = re.match(r"p=(\d+) .*\[2\] eta=([0-9.]+)", line)
    if mm:
        vp.append(int(mm.group(1)))
        ve.append(float(mm.group(2)))


def ceil6(x):
    return Decimal(x).quantize(Decimal("0.000001"), rounding=ROUND_CEILING)


def sum_cost(rows, lo, hi):
    """Exact decimal sum of the printed certified costs for lo <= p < hi."""
    return sum((r[2] for r in rows if lo <= r[0] < hi), Decimal(0))


def count(rows, lo, hi):
    return sum(1 for r in rows if lo <= r[0] < hi)


def fmt_delta(d):
    """delta for display: the shortest repr of the double, rounded half up to four decimals."""
    return str(Decimal(repr(d)).quantize(Decimal("0.0001"), rounding=ROUND_HALF_UP))


def fmt_int(n):
    return "{:,}".format(n).replace(",", "{,}")


def fmt_num(x, sig=4):
    """LaTeX number: fixed notation for 1e-3 <= x < 10, else a.bcd * 10^e."""
    if x == 0:
        return "0"
    if 1e-3 <= abs(x) < 10:
        digits = sig - 1 - int(math.floor(math.log10(abs(x))))
        return f"{x:.{max(digits, 0)}f}"
    e = int(math.floor(math.log10(abs(x))))
    mant = x / 10 ** e
    if round(mant, sig - 1) >= 10:
        mant /= 10
        e += 1
    return f"{mant:.{sig - 1}f}\\cdot 10^{{{e}}}"


# sanity: the dump sums are below the certified blocks
assert sum_cost(rows145, 0, 50) <= Decimal(cert145["A"])
assert sum_cost(rows145, 50, PX + 1) <= Decimal(cert145["B"])
assert sum_cost(rows16, 0, 50) <= Decimal(cert16["A"])
assert sum_cost(rows16, 50, PX + 1) <= Decimal(cert16["B"])
n_px = len(rows16)
assert n_px == len(rows145)

# ----------------------------------------------------------------------------------------------
# Table: both certificates by prime ranges (main text)
# ----------------------------------------------------------------------------------------------
coarse = [
    (2, 17, r"$p<17$"),
    (17, 50, r"$17\le p<50$"),
    (50, 200, r"$50\le p<200$"),
    (200, 2000, r"$200\le p<2{,}000$"),
    (2000, 20000, r"$2{,}000\le p<20{,}000$"),
    (20000, PX + 1, r"$20{,}000\le p\le 2\cdot 10^5$"),
]
lines = []
for lo, hi, lab in coarse:
    lines.append(f"{lab} & {fmt_int(count(rows16, lo, hi))} & {ceil6(sum_cost(rows145, lo, hi))} & "
                 f"{ceil6(sum_cost(rows16, lo, hi))} \\\\")
n_c16 = cert16["k"] - n_px
n_c145 = cert145["k"] - n_px
lines.append(r"$2\cdot 10^5<p\le P_{\max}$ & " + f"{fmt_int(n_c145)} / {fmt_int(n_c16)} & "
             + str(ceil6(Decimal(cert145["C"]))) + " & " + str(ceil6(Decimal(cert16["C"]))) + r" \\")
lines.append(r"\midrule")
lines.append(r"total, $p\le P_{\max}$ & " + f"{fmt_int(cert145['k'])} / {fmt_int(cert16['k'])} & "
             + str(ceil6(Decimal(cert145["eta"]))) + " & " + str(ceil6(Decimal(cert16["eta"]))) + r" \\")
with open(os.path.join(GEN, "table_budget.tex"), "w") as f:
    f.write("% generated by make_figures.py from certificate-14501/output and logs/ -- do not edit\n")
    f.write("\\begin{tabular}{@{}lrrr@{}}\n\\toprule\n")
    f.write("primes & number & $m=14{,}501$ & $m=16{,}000$ \\\\\n\\midrule\n")
    f.write("\n".join(lines) + "\n\\bottomrule\n\\end{tabular}\n")

# ----------------------------------------------------------------------------------------------
# Table: the m = 14,501 certificate by finer ranges (appendix)
# ----------------------------------------------------------------------------------------------
first_tau = min(r[0] for r in rows145 if r[1] == 3)
last_sbh = max(r[0] for r in rows145 if r[1] == 1)
edges145 = [2, 17, 31, 50, 100, 200, 500, 1000, 2000, first_tau, 20000, 50000, PX + 1]
how = {0: "first moment", 1: "S/B/H", 3: r"$\tau$-split"}
fine145 = []
tot_c = tot_m1 = Decimal(0)
for lo, hi in zip(edges145, edges145[1:]):
    idx = [r for r in rows145 if lo <= r[0] < hi]
    n = len(idx)
    ds = [d145(r[0]) for r in idx]
    dmin, dmax = min(ds), max(ds)
    sc = sum((r[2] for r in idx), Decimal(0))
    s1 = sum((r[3] for r in idx), Decimal(0))
    tot_c += sc
    tot_m1 += s1
    ws = sorted(set(r[1] for r in idx))
    meth = ", ".join(how[w] for w in ws)
    hi_lab = "2\\cdot 10^5" if hi == PX + 1 else fmt_int(hi)
    rel = "\\le" if hi == PX + 1 else "<"
    dr = fmt_delta(dmin) if abs(dmax - dmin) < 5e-5 else f"{fmt_delta(dmin)}--{fmt_delta(dmax)}"
    fine145.append(f"${fmt_int(lo)}\\le p{rel}{hi_lab}$ & {fmt_int(n)} & {dr} & {meth} & {ceil6(sc)} & "
                   f"{ceil6(s1)} \\\\")
fine145.append(r"\midrule")
fine145.append(f"$p\\le 2\\cdot 10^5$ & {fmt_int(n_px)} & & & {ceil6(tot_c)} & {ceil6(tot_m1)} \\\\")
fine145.append(r"$2\cdot 10^5<p\le 10^9$ & " + fmt_int(n_c145) + f" & {KNOTS145[-1][1]:.4f} & $\\tau$-split & "
               + str(ceil6(Decimal(cert145["C"]))) + r" & \\")
with open(os.path.join(GEN, "table_budget_main.tex"), "w") as f:
    f.write("% generated by make_figures.py from certificate-14501/output -- do not edit\n")
    f.write("\\begin{tabular}{@{}lrllrr@{}}\n\\toprule\n")
    f.write("primes & number & $\\delta_p$ & evaluation & $\\sum c_p$ & $\\sum\\mathbb{E}[U_p]$ \\\\\n\\midrule\n")
    f.write("\n".join(fine145) + "\n\\bottomrule\n\\end{tabular}\n")

# ----------------------------------------------------------------------------------------------
# Table: the knots of the m = 14,501 schedule (appendix), five (q, delta) pairs per row
# ----------------------------------------------------------------------------------------------
PER = 5
krows = []
for i in range(0, len(KNOTS145), PER):
    chunk = KNOTS145[i:i + PER]
    cells = []
    for q, d in chunk:
        cells.append(f"{fmt_int(q)} & {d:.6f}")
    cells += ["&"] * (PER - len(chunk))
    krows.append(" & ".join(cells) + r" \\")
with open(os.path.join(GEN, "table_knots_main.tex"), "w") as f:
    f.write("% generated by make_figures.py from certificate-14501/schedule/sched_14501.json -- do not edit\n")
    f.write("\\begin{tabular}{@{}" + "rl" * PER + "@{}}\n\\toprule\n")
    f.write(" & ".join(["$q$ & $\\delta$"] * PER) + r" \\" + "\n\\midrule\n")
    f.write("\n".join(krows) + "\n\\bottomrule\n\\end{tabular}\n")

# ----------------------------------------------------------------------------------------------
# Table: the m = 16,000 certificate between consecutive knots (appendix)
# ----------------------------------------------------------------------------------------------
edges = sorted(set([2, PSB16] + [p for p, _ in KNOTS16] + [PX + 1]))
fine = []
tot_c16 = tot_m1_16 = tot_bb16 = Decimal(0)
for lo, hi in zip(edges, edges[1:]):
    idx = [(i, r) for i, r in enumerate(rows16) if lo <= r[0] < hi]
    if not idx:
        continue
    n = len(idx)
    dmin = min(DEL16[i] for i, _ in idx)
    dmax = max(DEL16[i] for i, _ in idx)
    sc = sum((r[2] for _, r in idx), Decimal(0))
    s1 = sum(Decimal(repr(M1_16[i])) for i, _ in idx)
    sb = sum(Decimal(repr(BB16[i])) for i, _ in idx)
    tot_c16 += sc
    tot_m1_16 += s1
    tot_bb16 += sb
    hi_lab = "2\\cdot 10^5" if hi == PX + 1 else fmt_int(hi)
    rel = "\\le" if hi == PX + 1 else "<"
    dr = fmt_delta(dmin) if abs(dmax - dmin) < 5e-5 else f"{fmt_delta(dmin)}--{fmt_delta(dmax)}"
    fine.append(f"${fmt_int(lo)}\\le p{rel}{hi_lab}$ & {fmt_int(n)} & {dr} & {ceil6(sc)} & "
                f"{ceil6(s1)} & {ceil6(sb)} & {float(sb / sc):.2f} \\\\")
fine.append(r"\midrule")
fine.append(f"$p\\le 2\\cdot 10^5$ & {fmt_int(n_px)} & & {ceil6(tot_c16)} & {ceil6(tot_m1_16)} & "
            f"{ceil6(tot_bb16)} & {float(tot_bb16 / tot_c16):.2f} \\\\")
fine.append(r"$2\cdot 10^5<p\le 2\cdot 10^8$ & " + fmt_int(n_c16) + f" & {KNOTS16[-1][1]:.4f} & "
            + str(ceil6(Decimal(cert16["C"]))) + r" & & & \\")
with open(os.path.join(GEN, "table_budget_fine.tex"), "w") as f:
    f.write("% generated by make_figures.py from logs/dump16k.txt and logs/cert16k.txt -- do not edit\n")
    f.write("\\begin{tabular}{@{}lrlrrrr@{}}\n\\toprule\n")
    f.write("primes & number & $\\delta_p$ & $\\sum c_p$ & $\\sum\\mathbb{E}[U_p]$ & "
            "$\\sum b_p$ & ratio \\\\\n\\midrule\n")
    f.write("\n".join(fine) + "\n\\bottomrule\n\\end{tabular}\n")

# ----------------------------------------------------------------------------------------------
# Derived statistics quoted in the text
# ----------------------------------------------------------------------------------------------
cum_bb16 = np.cumsum(BB16)
cum_c16 = np.cumsum(COST16)
cum_c145 = np.cumsum(COST145)
i_pass = int(np.argmax(cum_bb16 >= 1.0))
p_pass = int(P16[i_pass])
ratio16 = BB16 / COST16


def rng(lo, hi):
    msk = (P16 >= lo) & (P16 < hi)
    return float(ratio16[msk].min()), float(ratio16[msk].max())


gA = rng(31, 50)
gB = rng(50, 2000)
gC = rng(2000, PX + 1)
n_cmp = sum(1 for r in rows16 if r[1] == 1)
n_m1 = sum(1 for r in rows16 if r[1] == 0)
below2k = sum_cost(rows145, 0, 2000)
share2k = below2k / Decimal(cert145["eta"])
with open(os.path.join(GEN, "derived.tex"), "w") as f:
    f.write("% generated by make_figures.py -- do not edit\n")
    f.write("% m = 16,000 certificate\n")
    f.write(f"\\newcommand{{\\nPrimesPX}}{{{fmt_int(n_px)}}}\n")
    f.write(f"\\newcommand{{\\nPrimesCmp}}{{{fmt_int(n_cmp)}}}\n")
    f.write(f"\\newcommand{{\\nPrimesMone}}{{{fmt_int(n_m1)}}}\n")
    f.write(f"\\newcommand{{\\nPrimesC}}{{{fmt_int(n_c16)}}}\n")
    f.write(f"\\newcommand{{\\sumCostPX}}{{{ceil6(sum_cost(rows16, 0, 10**9))}}}\n")
    f.write(f"\\newcommand{{\\sumMonePX}}{{{ceil6(tot_m1_16)}}}\n")
    f.write(f"\\newcommand{{\\sumBBPX}}{{{ceil6(tot_bb16)}}}\n")
    f.write(f"\\newcommand{{\\bbPassP}}{{{p_pass}}}\n")
    f.write(f"\\newcommand{{\\bbTotalPX}}{{{float(cum_bb16[-1]):.2f}}}\n")
    f.write(f"\\newcommand{{\\gainAmin}}{{{gA[0]:.2f}}}\\newcommand{{\\gainAmax}}{{{gA[1]:.2f}}}\n")
    f.write(f"\\newcommand{{\\gainBmin}}{{{gB[0]:.2f}}}\\newcommand{{\\gainBmax}}{{{gB[1]:.2f}}}\n")
    f.write(f"\\newcommand{{\\gainCmin}}{{{gC[0]:.2f}}}\\newcommand{{\\gainCmax}}{{{gC[1]:.2f}}}\n")
    f.write("% m = 14,501 certificate\n")
    f.write(f"\\newcommand{{\\nPrimesMoneMain}}{{{fmt_int(sum(1 for r in rows145 if r[1] == 0))}}}\n")
    f.write(f"\\newcommand{{\\nPrimesSBH}}{{{fmt_int(sum(1 for r in rows145 if r[1] == 1))}}}\n")
    f.write(f"\\newcommand{{\\nPrimesTauPX}}{{{fmt_int(sum(1 for r in rows145 if r[1] == 3))}}}\n")
    f.write(f"\\newcommand{{\\nPrimesCMain}}{{{fmt_int(n_c145)}}}\n")
    f.write(f"\\newcommand{{\\lastSBH}}{{{fmt_int(last_sbh)}}}\n")
    f.write(f"\\newcommand{{\\firstTau}}{{{fmt_int(first_tau)}}}\n")
    f.write(f"\\newcommand{{\\sumCostPXMain}}{{{ceil6(tot_c)}}}\n")
    f.write(f"\\newcommand{{\\sumMonePXMain}}{{{ceil6(tot_m1)}}}\n")
    f.write(f"\\newcommand{{\\sumBelowTwoK}}{{{ceil6(below2k)}}}\n")
    f.write(f"\\newcommand{{\\shareBelowTwoK}}{{{int(share2k * 100)}}}\n")
    f.write(f"\\newcommand{{\\nKnotsMain}}{{{len(KNOTS145)}}}\n")

# ----------------------------------------------------------------------------------------------
# Figures (static PDF; light surface; the first three categorical slots of the reference palette,
# validated all-pairs; aqua is below 3:1 contrast, so every curve is also labelled directly)
# ----------------------------------------------------------------------------------------------
BLUE, ORANGE, AQUA = "#2a78d6", "#eb6834", "#1baf7a"     # m = 14,501 / m = 16,000 / BBMST at m = 16,000
INK, INK2, GRID = "#0b0b0b", "#52514e", "#e2e1dc"
plt.rcParams.update({
    "font.family": "serif", "font.serif": ["cmr10", "STIXGeneral", "DejaVu Serif"],
    "mathtext.fontset": "cm", "axes.formatter.use_mathtext": True, "axes.unicode_minus": False,
    "font.size": 9, "axes.labelsize": 9, "xtick.labelsize": 8, "ytick.labelsize": 8,
    "legend.fontsize": 8, "axes.edgecolor": INK2, "axes.linewidth": 0.6,
    "xtick.color": INK2, "ytick.color": INK2, "axes.labelcolor": INK, "text.color": INK,
    "xtick.major.width": 0.6, "ytick.major.width": 0.6, "xtick.minor.width": 0.4,
    "pdf.fonttype": 42,
})


def style(ax):
    ax.grid(True, which="major", color=GRID, linewidth=0.5, linestyle="-")
    ax.set_axisbelow(True)
    for s in ("top", "right"):
        ax.spines[s].set_visible(False)


def dot(ax, x, y, color):
    ax.plot([x], [y], "o", ms=4.5, color=color, mec="white", mew=1.2, zorder=5)


# Figure 1: running totals
fig, ax = plt.subplots(figsize=(6.2, 3.4))
style(ax)
eta145 = float(cert145["eta"])
eta16 = float(cert16["eta"])
ax.plot(P145, cum_c145, color=BLUE, lw=1.6, solid_joinstyle="round", label=r"$m=14{,}501$ (Theorem 1.1)")
ax.plot([P145[-1], 1e9], [cum_c145[-1], eta145], color=BLUE, lw=1.2, ls=(0, (1.5, 1.5)))
xs = np.concatenate([P16, np.array(vp, dtype=float)])
ys = np.concatenate([cum_c16, np.array(ve)])
ax.plot(xs, ys, color=ORANGE, lw=1.6, solid_joinstyle="round", label=r"$m=16{,}000$ (Theorem 1.3)")
clip = cum_bb16 <= 1.12
last = int(np.argmax(~clip)) if (~clip).any() else len(cum_bb16)
ax.plot(P16[: last + 1], np.minimum(cum_bb16[: last + 1], 1.12), color=AQUA, lw=1.6, ls=(0, (4, 1.5)),
        label=r"BBMST moment bounds, $m=16{,}000$")
ax.axhline(1.0, color=INK, lw=0.8)
ax.text(2e4, 1.015, "budget: the total must stay below 1", color=INK2, fontsize=8, va="bottom")
dot(ax, P16[i_pass], cum_bb16[i_pass], AQUA)
ax.annotate(f"BBMST: exceeds 1 at $p={p_pass}$", xy=(P16[i_pass], cum_bb16[i_pass]), xytext=(5e2, 1.075),
            fontsize=8, color=INK2, va="center", arrowprops=dict(arrowstyle="-", color=INK2, lw=0.5))
eta145_disp = str(ceil6(Decimal(cert145["eta"])))
eta16_disp = str(ceil6(Decimal(cert16["eta"])))
dot(ax, 1e9, eta145, BLUE)
dot(ax, 2e8, eta16, ORANGE)
ax.annotate(f"$m=14{{,}}501$: total $\\leq {eta145_disp}$ at $p=10^9$", xy=(1e9, eta145), xytext=(1e9, 0.80),
            fontsize=8, color=INK2, ha="right", va="center",
            arrowprops=dict(arrowstyle="-", color=INK2, lw=0.5, relpos=(1.0, 0.5)))
ax.annotate(f"$m=16{{,}}000$: total $\\leq {eta16_disp}$ at $p=2\\cdot 10^8$", xy=(2e8, eta16),
            xytext=(2e8, 0.89), fontsize=8, color=INK2, ha="right", va="center",
            arrowprops=dict(arrowstyle="-", color=INK2, lw=0.5, relpos=(1.0, 0.5)))
ax.set_xscale("log")
ax.set_xlim(1.8, 2e9)
ax.set_ylim(0, 1.12)
ax.set_xlabel(r"prime $p$ (log scale)")
ax.set_ylabel(r"running total of the loss bounds")
ax.legend(loc="lower right", frameon=False, bbox_to_anchor=(1.0, 0.08))
fig.tight_layout()
fig.savefig(os.path.join(FIG, "cumulative_loss.pdf"))
plt.close(fig)

# Figure 2: (a) the two delta schedules, (b) gain factor b_p / c_p at m = 16,000
fig, (a1, a2) = plt.subplots(2, 1, figsize=(6.2, 3.8), sharex=True,
                             gridspec_kw={"height_ratios": [1.0, 1.0], "hspace": 0.12})
style(a1)
style(a2)
grid = np.geomspace(2, 1e9, 4000)
g16 = np.sort(np.concatenate([grid, [PSB16 - 1e-9, PSB16, PD16 - 1e-9, PD16]]))
g145 = np.sort(np.concatenate([grid, [PD145 - 1e-9, PD145]]))
a1.plot(g145, [d145(float(q)) for q in g145], color=BLUE, lw=1.3, solid_joinstyle="round",
        label=r"$m=14{,}501$ (" + str(len(KNOTS145)) + " knots)")
a1.plot(g16, [d16(float(q)) for q in g16], color=ORANGE, lw=1.3, solid_joinstyle="round",
        label=r"$m=16{,}000$ (" + str(len(KNOTS16)) + " knots)")
a1.plot([k for k, _ in KNOTS16], [d for _, d in KNOTS16], "o", ms=3.8, color=ORANGE, mec="white", mew=1.0,
        zorder=5)
a1.set_ylabel(r"distortion $\delta_p$")
a1.set_ylim(-0.01, 0.5)
a1.text(1e5, 0.475, r"$0.46$ for $p\geq 2\cdot 10^5$", fontsize=7.5, color=INK2)
a1.text(1e6, 0.36, r"$0.4092$ for $p\geq 5\cdot 10^4$", fontsize=7.5, color=INK2)
a1.legend(loc="lower right", frameon=False)
a1.text(0.005, 0.97, "(a)", transform=a1.transAxes, fontsize=8, color=INK, va="top")
msk = P16 >= 31
a2.plot(P16[msk], ratio16[msk], color=ORANGE, lw=0.9)
a2.set_ylabel(r"$b_p/c_p$ at $m=16{,}000$")
a2.set_ylim(0, 11.5)
a2.text(40, 9.3, r"$b_p$: BBMST moment bound; $c_p$: comparison bound" + "\n(same schedule, certified inputs)",
        fontsize=7.5, color=INK2)
a2.text(0.005, 0.97, "(b)", transform=a2.transAxes, fontsize=8, color=INK, va="top")
a2.set_xscale("log")
a2.set_xlim(1.8, 2e9)
a2.set_xlabel(r"prime $p$ (log scale)")
a2.axvline(2e5, color=INK2, lw=0.5)
fig.subplots_adjust(left=0.1, right=0.98, top=0.98, bottom=0.12)
fig.savefig(os.path.join(FIG, "schedule_gain.pdf"))
plt.close(fig)

print("m=14501: eta_up", cert145["eta"], "A", cert145["A"], "B", cert145["B"], "C", cert145["C"], "k", cert145["k"])
print("m=16000: eta_up", cert16["eta"], "A", cert16["A"], "B", cert16["B"], "C", cert16["C"], "k", cert16["k"])
print("primes <= 2e5:", n_px, " (16k) comparison:", n_cmp, " first moment:", n_m1)
print("14501: SBH last", last_sbh, "tau first", first_tau, "share p<2000", float(share2k))
print("BBMST-type (16k): exceeds 1 at p =", p_pass, "; total at 2e5 = %.4f" % cum_bb16[-1])
print("gain ranges: 31-50 %.3f-%.3f, 50-2000 %.3f-%.3f, 2000-2e5 %.3f-%.3f" % (gA + gB + gC))
print("sampled running totals above 2e5 (16k):", len(vp), " sampled primes above 2e5 (14501):", len(samp145))
