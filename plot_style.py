"""Shared Inter typography and print-resolution exports for research figures."""
from pathlib import Path

import matplotlib as mpl
from matplotlib import font_manager

FONT_DIR = Path(__file__).resolve().parent / "assets" / "fonts" / "inter"
EXPORT_DPI = 600


def configure_style():
    """Register bundled fonts; do not depend on fonts installed on the host."""
    for face in ("Regular", "Bold"):
        font_manager.fontManager.addfont(str(FONT_DIR / f"Inter-{face}.ttf"))
    mpl.rcParams.update({
        "font.family": "Inter",
        "font.sans-serif": ["Inter"],
        "font.size": 12,
        "axes.titlesize": 14,
        "axes.labelsize": 12,
        "axes.titleweight": "bold",
        "axes.spines.top": False,
        "axes.spines.right": False,
        "axes.labelcolor": "#252525",
        "text.color": "#252525",
        "xtick.color": "#555555",
        "ytick.color": "#555555",
        "legend.fontsize": 11,
        "mathtext.fontset": "custom",
        "mathtext.rm": "Inter",
        "mathtext.it": "Inter",
        "mathtext.bf": "Inter:weight=bold",
        "mathtext.bfit": "Inter:weight=bold",
        "mathtext.sf": "Inter",
        "mathtext.tt": "Inter",
        "mathtext.cal": "Inter",
        "mathtext.default": "regular",
        "mathtext.fallback": None,
        "figure.facecolor": "white",
        "savefig.facecolor": "white",
        "savefig.dpi": EXPORT_DPI,
        # Outline SVG glyphs so the exact Inter face survives sharing.
        "svg.fonttype": "path",
        "svg.hashsalt": "lean-stuff-inter-figures-v1",
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
    })
    resolved = Path(font_manager.findfont("Inter", fallback_to_default=False))
    if resolved.parent != FONT_DIR:
        raise RuntimeError(f"Expected the bundled Inter font, resolved {resolved}")


def save_figure(fig, stem):
    """Write 600-dpi PNG and vector SVG/PDF files with the same layout."""
    stem = Path(stem)
    stem.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(stem.with_suffix(".png"), dpi=EXPORT_DPI)
    svg = stem.with_suffix(".svg")
    fig.savefig(svg, metadata={"Date": None})
    # Matplotlib adds insignificant whitespace inside SVG path attributes.
    svg.write_text("\n".join(line.rstrip() for line in svg.read_text().splitlines()) + "\n")
    fig.savefig(stem.with_suffix(".pdf"), metadata={
        "Creator": "Matplotlib; bundled Inter typography",
        "CreationDate": None,
        "ModDate": None,
    })
