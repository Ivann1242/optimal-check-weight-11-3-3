"""Figure 2: the [[12,3,3]] stabilizer code with weight-4 generators.

Draws the 9 x 12 generator matrix (rows: generators, columns: qubits) and checks,
independently of the plot, that the generators commute, are independent over GF(2),
have weight 4, and that the 36 single-qubit syndromes are nonzero and pairwise distinct.
"""
import sys
from itertools import combinations
from pathlib import Path

import matplotlib as mpl
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "nature-skills/skills/nature-figure/scripts"))
from audit_panel_alignment import require_matplotlib_panel_alignment  # noqa: E402

GENS = ["IIIIIIZZIIZZ", "IIIIIIIIZZXX", "ZZIIIIIIXXII", "IIIIZZXXIIII", "IIIZIXIYIIIX",
        "ZIZIXXIIIIII", "IZXXIZIIIIII", "IXIYIIIIIYIZ", "XIIIYIZIZIII"]
BITS = {"I": (0, 0), "X": (1, 0), "Z": (0, 1), "Y": (1, 1)}


def check():
    n, m = len(GENS[0]), len(GENS)
    vec = [[BITS[c] for c in g] for g in GENS]
    for a, b in combinations(vec, 2):
        assert sum(p[0] * q[1] + p[1] * q[0] for p, q in zip(a, b)) % 2 == 0
    assert all(sum(c != "I" for c in g) == 4 for g in GENS)
    rows = [int("".join(str(x) for p in v for x in p), 2) for v in vec]
    basis = []
    for r in rows:
        for b in basis:
            r = min(r, r ^ b)
        assert r
        basis.append(r)
    syn = set()
    for j in range(n):
        for e in [(0, 1), (1, 0), (1, 1)]:
            s = tuple((e[0] * v[j][1] + e[1] * v[j][0]) % 2 for v in vec)
            assert any(s) and s not in syn
            syn.add(s)
    return n, m


def main():
    n, m = check()
    mpl.rcParams.update({
        "font.family": "sans-serif",
        "font.sans-serif": ["Arial", "Helvetica", "DejaVu Sans", "sans-serif"],
        "pdf.fonttype": 42, "svg.fonttype": "none", "font.size": 8,
    })
    colors = {"X": "#0072B2", "Z": "#D55E00", "Y": "#009E73"}
    fig, ax = plt.subplots(figsize=(9.0 / 2.54, 7.2 / 2.54))
    for i, g in enumerate(GENS):
        for j, c in enumerate(g):
            face = colors.get(c, "white")
            ax.add_patch(Rectangle((j, m - 1 - i), 1, 1, facecolor=face,
                                   edgecolor="#BBBBBB", lw=0.5))
            if c != "I":
                ax.text(j + 0.5, m - 0.5 - i, c, ha="center", va="center",
                        color="white", fontsize=8, fontweight="bold")
    ax.set_xlim(0, n)
    ax.set_ylim(0, m)
    ax.set_aspect("equal")
    ax.set_xticks([j + 0.5 for j in range(n)])
    ax.set_xticklabels([str(j + 1) for j in range(n)])
    ax.set_yticks([m - 0.5 - i for i in range(m)])
    ax.set_yticklabels([rf"$g_{{{i + 1}}}$" for i in range(m)])
    ax.tick_params(length=0)
    for side in ax.spines.values():
        side.set_visible(False)
    ax.set_xlabel("Qubit")
    fig.canvas.draw()
    require_matplotlib_panel_alignment(
        fig, json_out=str(HERE / "fig_code12.alignment.json"),
        overlay_svg=str(HERE / "fig_code12.alignment.svg"),
        tolerance_pt=1.5, gutter_tolerance_pt=1.5, strict=True)
    for ext in ("pdf", "svg"):
        fig.savefig(HERE / f"fig_code12.{ext}", bbox_inches="tight")
    fig.savefig(HERE / "fig_code12.png", dpi=600, bbox_inches="tight")
    print("checks passed:", n, "qubits,", m, "generators")


if __name__ == "__main__":
    main()
