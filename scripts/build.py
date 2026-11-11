#!/usr/bin/env python3
"""
Profile art generator for github.com/aaatishphadte
--------------------------------------------------
Builds every SVG in ../assets from the CONFIG block below. No third-party
image services: every graphic is drawn here and committed to the repo.

  python scripts/build.py           # rebuild everything from CONFIG
  python scripts/build.py --live    # also pull fresh stats from GitHub
                                    # (needs GITHUB_TOKEN; the Action does this daily)

Requires:  pip install fonttools brotli
Fonts (SIL Open Font License) live in scripts/fonts and are subset + embedded
into each SVG, so the type renders identically for every visitor.
"""
from __future__ import annotations

import base64
import hashlib
import io
import json
import math
import os
import random
import re
import sys
import urllib.request
from collections import defaultdict
from datetime import date, datetime, timedelta, timezone
from pathlib import Path
from xml.sax.saxutils import escape

from fontTools import subset as ft_subset
from fontTools.ttLib import TTFont

ROOT = Path(__file__).resolve().parent.parent
ASSETS = ROOT / "assets"
FONT_DIR = Path(__file__).resolve().parent / "fonts"

# ════════════════════════════════════════════════════════════════════
#  CONFIG — edit this block, re-run the script, commit /assets
# ════════════════════════════════════════════════════════════════════
CONFIG = {
    "username": "aaatishphadte",
    "name": "Dattatray Phadte",
    "alias": "a.k.a. Atish",
    "kicker": "TECHNICAL FOUNDER  ·  GOA, BHARAT",
    "coords": "15.3°N  74.1°E",
    "typing": [
        "building games at DataTree Studios",
        "shipping AI agents at BooleanChitra",
        "learning Gen-AI, MCP & agentic automation",
    ],
    "buttons": [
        # (file-slug, label)  — links are set in README.md
        ("booleanchitra", "BooleanChitra"),
        ("portfolio", "Portfolio"),
        ("repos", "All repositories"),
    ],
    "ventures": {
        "datatree": {
            "kicker": "01 · GAME STUDIO",
            "title": ("DataTree", "Studios"),
            "tagline": "Indie games, grown in Goa.",
            "chips": ["GAMES", "INTERACTIVE STORIES", "GEN-AI PLAY"],
            "caption": "tree.depth = 4",
            "footer_right": "NOW BUILDING",
        },
        "booleanchitra": {
            "kicker": "02 · AI SOFTWARE AGENCY",
            "title": ("Boolean", "Chitra"),
            "tagline": "AI agents & automation, built in Goa.",
            "chips": ["AI AGENTS", "AUTOMATION", "MCP", "LLM APPS"],
            "caption": "chitra (n.) — picture",
            "footer_right": "VISIT",
        },
    },
    "projects": [
        {
            "slug": "rpg",
            "name": "Gen-AI-RPG-Game",
            "desc": "A text adventure you direct and star in, while the AI brings the story to life.",
            "lang": ("Jupyter Notebook", "#DA5B0B"),
            "tags": "GEN-AI · GAME · STORYTELLING",
        },
        {
            "slug": "pdf",
            "name": "ai-pdf-chatbot-langchain",
            "desc": "AI PDF chatbot agent built with LangChain and LangGraph.",
            "lang": ("TypeScript", "#3178C6"),
            "tags": "LANGGRAPH · RAG · FORK",
        },
        {
            "slug": "scraper",
            "name": "Ecommerce-Product-Scrapper",
            "desc": "Crawls shopping sites and scrapes product URLs.",
            "lang": ("TypeScript", "#3178C6"),
            "tags": "SCRAPING · AUTOMATION",
        },
        {
            "slug": "crawler",
            "name": "ecommerce-crawler",
            "desc": "Crawler for discovering product URLs on e-commerce websites.",
            "lang": ("Open source", "#8A8DB0"),
            "tags": "CRAWLING · DATA",
        },
    ],
    "toolkit": [
        # (row label, accent, items)
        ("AI / AGENTS", "saffron", ["LangChain", "LangGraph", "MCP", "RAG", "LLM APIs", "Prompt design"]),
        ("LANGUAGES", "teal", ["Python", "TypeScript", "Jupyter"]),
        ("SHIP", "cream", ["Node.js", "Cloudflare Workers", "Web scraping", "Git & GitHub"]),
        ("PLAY", "leaf", ["Game design", "Interactive fiction", "AI-driven narrative"]),
    ],
    # Seed numbers shown until the first Action run replaces them with live data.
    "seed_stats": {
        "contributions": 303,
        "current_streak": None,
        "longest_streak": None,
        "repos": 16,
        "languages": [("TypeScript", "#3178C6", 1), ("Jupyter Notebook", "#DA5B0B", 1), ("Python", "#3572A5", 1)],
        "languages_basis": "by repo count",
    },
    "footer_line": "Small, useful work over vague claims.",
    "footer_sub": "DATATREE STUDIOS  ×  BOOLEANCHITRA  ·  MADE IN GOA, BHARAT",
}

# ════════════════════════════════════════════════════════════════════
#  DESIGN TOKENS
# ════════════════════════════════════════════════════════════════════
C = {
    "ink": "#07080F",
    "ink2": "#0E1022",
    "panel": "#121430",
    "line": "#262A4D",
    "chip": "#171A3A",
    "cream": "#F6EFE4",
    "muted": "#A6A8C6",
    "dim": "#6C6F95",
    "saffron": "#FF9933",
    "gold": "#FFC86B",
    "coral": "#FF5E62",
    "rose": "#D9467A",
    "plum": "#3A1847",
    "teal": "#2EC4B6",
    "leaf": "#8BE28B",
    "palm": "#05040B",
}

FONTS = {
    "sg4": "space-grotesk-latin-400-normal.woff2",
    "sg5": "space-grotesk-latin-500-normal.woff2",
    "sg7": "space-grotesk-latin-700-normal.woff2",
    "jb4": "jetbrains-mono-latin-400-normal.woff2",
    "jb7": "jetbrains-mono-latin-700-normal.woff2",
    "px": "silkscreen-latin-400-normal.woff2",
    "is": "instrument-serif-latin-400-italic.woff2",
}
FALLBACK = {
    "sg": "'Segoe UI', Helvetica, Arial, sans-serif",
    "jb": "ui-monospace, SFMono-Regular, Menlo, Consolas, monospace",
    "px": "ui-monospace, monospace",
    "is": "Georgia, 'Times New Roman', serif",
}


# ════════════════════════════════════════════════════════════════════
#  FONT + SVG HELPERS
# ════════════════════════════════════════════════════════════════════
class Font:
    _cache: dict[str, "Font"] = {}

    def __init__(self, key: str):
        self.key = key
        self.path = FONT_DIR / FONTS[key]
        self.tt = TTFont(self.path)
        self.cmap = self.tt.getBestCmap()
        self.hmtx = self.tt["hmtx"].metrics
        self.upem = self.tt["head"].unitsPerEm
        self._subsets: dict[frozenset, str] = {}

    @classmethod
    def get(cls, key: str) -> "Font":
        if key not in cls._cache:
            cls._cache[key] = Font(key)
        return cls._cache[key]

    def width(self, text: str, size: float, ls: float = 0) -> float:
        w = 0.0
        for ch in text:
            g = self.cmap.get(ord(ch))
            w += (self.hmtx[g][0] if g else self.upem * 0.6) / self.upem * size
        return w + ls * max(len(text) - 1, 0)

    def data_uri(self, chars: set[str]) -> str:
        key = frozenset(chars)
        if key not in self._subsets:
            opts = ft_subset.Options()
            opts.flavor = "woff2"
            opts.layout_features = ["kern", "liga", "calt"]
            opts.name_IDs = []
            opts.notdef_outline = False
            f = TTFont(self.path)
            sub = ft_subset.Subsetter(opts)
            sub.populate(unicodes=[ord(c) for c in chars if ord(c) in self.cmap] or [32])
            sub.subset(f)
            buf = io.BytesIO()
            f.flavor = "woff2"
            f.save(buf)
            self._subsets[key] = base64.b64encode(buf.getvalue()).decode()
        return self._subsets[key]


def fam(key: str) -> str:
    return f"f{key}, {FALLBACK[key[:2]]}"


def n(v: float) -> str:
    """compact number formatting for SVG attributes"""
    s = f"{v:.2f}".rstrip("0").rstrip(".")
    return "0" if s in ("-0", "") else s


class Svg:
    def __init__(self, w: int, h: int, title: str, desc: str = ""):
        self.w, self.h, self.title, self.desc = w, h, title, desc
        self.defs: list[str] = []
        self.body: list[str] = []
        self.css: list[str] = []
        self.used: dict[str, set[str]] = defaultdict(set)
        self.meta = ""

    def add(self, s: str):
        self.body.append(s)

    def text(self, x, y, s, key, size, fill, anchor="start", ls=0.0, cls="", extra="", raw=False) -> str:
        self.used[key].update(s)
        attrs = [f'x="{n(x)}"', f'y="{n(y)}"', f'font-family="{fam(key)}"', f'font-size="{n(size)}"', f'fill="{fill}"']
        if anchor != "start":
            attrs.append(f'text-anchor="{anchor}"')
        if ls:
            attrs.append(f'letter-spacing="{n(ls)}"')
        if cls:
            attrs.append(f'class="{cls}"')
        if extra:
            attrs.append(extra)
        body = s if raw else escape(s)
        return f"<text {' '.join(attrs)}>{body}</text>"

    def tspan_text(self, x, y, parts, anchor="start", extra="") -> str:
        """parts = [(text, key, size, fill, dx)]"""
        spans = []
        for t, key, size, fill, dx in parts:
            self.used[key].update(t)
            spans.append(
                f'<tspan font-family="{fam(key)}" font-size="{n(size)}" fill="{fill}"'
                + (f' dx="{n(dx)}"' if dx else "")
                + f">{escape(t)}</tspan>"
            )
        a = f' text-anchor="{anchor}"' if anchor != "start" else ""
        return f'<text x="{n(x)}" y="{n(y)}"{a} {extra}>{"".join(spans)}</text>'

    def render(self) -> str:
        faces = []
        for key, chars in sorted(self.used.items()):
            uri = Font.get(key).data_uri(chars | {" "})
            faces.append(
                f"@font-face{{font-family:f{key};src:url(data:font/woff2;base64,{uri}) format('woff2');font-display:block}}"
            )
        style = "".join(faces) + "".join(self.css)
        desc = f"<desc>{escape(self.desc)}</desc>" if self.desc else ""
        return (
            f'<svg xmlns="http://www.w3.org/2000/svg" width="{self.w}" height="{self.h}" '
            f'viewBox="0 0 {self.w} {self.h}" fill="none" role="img" aria-labelledby="title">'
            f"{self.meta}<title id=\"title\">{escape(self.title)}</title>{desc}"
            f"<style>{style}</style><defs>{''.join(self.defs)}</defs>{''.join(self.body)}</svg>\n"
        )


def write(name: str, svg: Svg):
    out = ASSETS / name
    out.write_text(svg.render(), encoding="utf-8")
    print(f"  ✓ {name:<34} {out.stat().st_size/1024:6.1f} KB")


def cells_path(cells, p, ox=0.0, oy=0.0) -> str:
    """Turn a set of grid cells into one compact path (merges horizontal runs)."""
    rows = defaultdict(list)
    for gx, gy in cells:
        rows[gy].append(gx)
    d = []
    for gy, xs in rows.items():
        xs = sorted(set(xs))
        start = prev = xs[0]
        for x in xs[1:] + [None]:
            if x is not None and x == prev + 1:
                prev = x
                continue
            d.append(f"M{n(ox + start * p)} {n(oy + gy * p)}h{n((prev - start + 1) * p)}v{n(p)}h{n(-(prev - start + 1) * p)}z")
            if x is not None:
                start = prev = x
    return "".join(d)


def bitmap_cells(rows: list[str]):
    return {(x, y) for y, r in enumerate(rows) for x, ch in enumerate(r) if ch == "#"}


def arrow(x, y, s, color, sw=1.6) -> str:
    """north-east arrow ↗ drawn as a path (fonts here have no arrow glyphs)"""
    return (
        f'<path d="M{n(x)} {n(y + s)}L{n(x + s)} {n(y)}M{n(x + s * 0.3)} {n(y)}H{n(x + s)}V{n(y + s * 0.7)}" '
        f'stroke="{color}" stroke-width="{sw}" stroke-linecap="round" stroke-linejoin="round"/>'
    )


HEART = [".##.##.", "#######", "#######", ".#####.", "..###..", "...#..."]


# ════════════════════════════════════════════════════════════════════
#  HERO
# ════════════════════════════════════════════════════════════════════
def palm_cells(bx, by, cx, cy, p, frond_len, bend, angles, rng):
    """Procedural pixel palm: curved trunk + drooping fronds, snapped to a p-grid."""
    trunk, fronds = set(), set()
    steps = int(math.hypot(cx - bx, cy - by) / p * 2)
    for i in range(steps + 1):
        t = i / steps
        x = bx + (cx - bx) * t + bend * math.sin(math.pi * t)
        y = by + (cy - by) * t
        gx, gy = round(x / p), round(y / p)
        trunk |= {(gx, gy), (gx + 1, gy)}
        if t < 0.12:
            trunk.add((gx - 1, gy))
    for a in angles:
        L = frond_len * rng.uniform(0.85, 1.08)
        rad = math.radians(a)
        droop = rng.uniform(0.62, 0.82)
        m = int(L / p * 4)
        maxw = max(0.9, L / p * 0.06)
        prev = None
        for i in range(0, m + 1):
            s_ = i / m
            x = cx + L * s_ * math.cos(rad)
            y = cy + L * s_ * math.sin(rad) + droop * L * s_ * s_
            if prev is not None:
                tx, ty = x - prev[0], y - prev[1]
                tl = math.hypot(tx, ty) or 1
                nx, ny = -ty / tl, tx / tl
                if ny < 0:
                    nx, ny = -nx, -ny  # normal points downward
                # leaf profile: fat in the middle, tapering to a point; serrated underside
                w = maxw * math.sin(math.pi * min(1, s_ * 1.05)) ** 0.7
                below = w * (1.0 if i % 3 else 1.9)
                above = w * 0.3
                k = -above
                while k <= below:
                    fronds.add((round((x + nx * k * p) / p), round((y + ny * k * p) / p)))
                    k += 0.5
            fronds.add((round(x / p), round(y / p)))
            prev = (x, y)
    gcx, gcy = round(cx / p), round(cy / p)
    fronds |= {(gcx - 1, gcy), (gcx, gcy), (gcx + 1, gcy), (gcx + 2, gcy), (gcx, gcy - 1), (gcx + 1, gcy - 1)}
    nuts = {(gcx - 1, gcy + 1), (gcx, gcy + 2), (gcx + 2, gcy + 1), (gcx + 1, gcy + 2)}
    return trunk, fronds, nuts


def typing_timeline(lines, char_w, t_char=0.06, hold=1.9, t_erase=0.022, gap=0.45):
    """Discrete keyframes for a typewriter that cycles through lines."""
    slots, t = [], 0.0
    for s in lines:
        start = t
        typed = start + len(s) * t_char
        held = typed + hold
        erased = held + len(s) * t_erase
        slots.append((start, s, typed, held, erased))
        t = erased + gap
    total = t
    per_line, cursor = [], [(0.0, 0.0)]
    for idx, (start, s, typed, held, erased) in enumerate(slots):
        ev = [(0.0, 0.0)]
        for c in range(1, len(s) + 1):
            ev.append((start + c * t_char, c * char_w))
        for c in range(len(s) - 1, -1, -1):
            ev.append((held + (len(s) - c) * t_erase, c * char_w))
        per_line.append(ev)
        cursor += ev[1:]

    def to_anim(ev):
        ev = sorted(ev)
        kt, vals, last_t = [], [], -1.0
        for tt, v in ev:
            f = round(tt / total, 5)
            if f <= last_t:
                f = round(last_t + 0.00001, 5)
            if f >= 1:
                break
            kt.append(f)
            vals.append(v)
            last_t = f
        return ";".join(n(k) if k else "0" for k in kt), ";".join(n(v) for v in vals)

    return total, [to_anim(e) for e in per_line], to_anim(cursor)


def build_hero():
    W, H, HZ = 1000, 400, 268
    rng = random.Random(7)
    s = Svg(W, H, "Dattatray 'Atish' Phadte — Technical founder · DataTree Studios & BooleanChitra · Goa, Bharat",
            "A pixel-art Goan sunset over the Arabian Sea with palm silhouettes.")
    s.defs += [
        f'<clipPath id="frame"><rect width="{W}" height="{H}" rx="22"/></clipPath>',
        '<linearGradient id="sky" x1="0" y1="0" x2="0" y2="1">'
        f'<stop offset="0" stop-color="{C["ink"]}"/><stop offset=".42" stop-color="#140F2C"/>'
        f'<stop offset=".78" stop-color="{C["plum"]}"/><stop offset="1" stop-color="#6E2652"/></linearGradient>',
        '<linearGradient id="sea" x1="0" y1="0" x2="0" y2="1">'
        f'<stop offset="0" stop-color="#2B1240"/><stop offset=".55" stop-color="#120D26"/><stop offset="1" stop-color="{C["ink"]}"/></linearGradient>',
        '<linearGradient id="sun" x1="0" y1="0" x2="0" y2="1">'
        f'<stop offset="0" stop-color="{C["gold"]}"/><stop offset=".38" stop-color="{C["saffron"]}"/>'
        f'<stop offset=".72" stop-color="{C["coral"]}"/><stop offset="1" stop-color="{C["rose"]}"/></linearGradient>',
        '<radialGradient id="glow"><stop offset="0" stop-color="#FF9933" stop-opacity=".55"/>'
        '<stop offset=".45" stop-color="#FF5E62" stop-opacity=".18"/><stop offset="1" stop-color="#FF5E62" stop-opacity="0"/></radialGradient>',
        '<linearGradient id="hz" x1="0" y1="0" x2="1" y2="0"><stop offset="0" stop-color="#FF9933" stop-opacity="0"/>'
        '<stop offset=".8" stop-color="#FFB45C" stop-opacity=".9"/><stop offset="1" stop-color="#FF9933" stop-opacity=".2"/></linearGradient>',
        '<linearGradient id="shade" x1="0" y1="0" x2="1" y2="0"><stop offset="0" stop-color="#07080F" stop-opacity=".88"/>'
        '<stop offset=".42" stop-color="#07080F" stop-opacity=".55"/><stop offset=".66" stop-color="#07080F" stop-opacity="0"/></linearGradient>',
        '<linearGradient id="streak" x1="0" y1="0" x2="1" y2="0"><stop offset="0" stop-color="#F6EFE4" stop-opacity="0"/>'
        '<stop offset="1" stop-color="#F6EFE4"/></linearGradient>',
        '<pattern id="scan" width="4" height="4" patternUnits="userSpaceOnUse"><rect width="4" height="1" fill="#000" opacity=".22"/></pattern>',
        '<radialGradient id="vig" cx=".5" cy=".5" r=".75"><stop offset=".6" stop-color="#000" stop-opacity="0"/>'
        '<stop offset="1" stop-color="#000" stop-opacity=".55"/></radialGradient>',
    ]
    # sun mask with retro stripes in its lower half
    SX, SR = 800, 118
    stripes = []
    y, gap, k = HZ - SR * 0.52, 2.0, 0
    while y < HZ:
        stripes.append(f'<rect x="{SX - SR - 4}" y="{n(y)}" width="{SR * 2 + 8}" height="{n(gap)}" fill="#000"/>')
        y += 11 - k * 0.6
        gap += 1.6
        k += 1
    s.defs.append(
        f'<mask id="sunm"><rect width="{W}" height="{H}" fill="#000"/>'
        f'<circle cx="{SX}" cy="{HZ}" r="{SR}" fill="#fff"/>{"".join(stripes)}'
        f'<rect y="{HZ}" width="{W}" height="{H - HZ}" fill="#000"/></mask>'
    )

    s.css.append(
        "@keyframes tw{0%,100%{opacity:.15}50%{opacity:1}}"
        ".tw{animation:tw 3.2s ease-in-out infinite}"
        "@keyframes glow{0%,100%{opacity:.75}50%{opacity:1}}.glow{animation:glow 6s ease-in-out infinite}"
        "@keyframes rf{0%,100%{transform:translateX(0);opacity:.95}50%{transform:translateX(7px);opacity:.5}}"
        ".rf{animation:rf 3.6s ease-in-out infinite}"
        "@keyframes sway{0%,100%{transform:rotate(-1.6deg)}50%{transform:rotate(1.8deg)}}"
        "@keyframes sway2{0%,100%{transform:rotate(1.4deg)}50%{transform:rotate(-1.8deg)}}"
        "@keyframes shoot{0%{transform:translate(0,0);opacity:0}1.5%{opacity:1}9%{transform:translate(-300px,120px);opacity:0}100%{transform:translate(-300px,120px);opacity:0}}"
        ".shoot{animation:shoot 11s linear 2s infinite;opacity:0}"
        "@keyframes blink{0%,49%{opacity:1}50%,100%{opacity:0}}.blink{animation:blink 1.1s steps(1) infinite}"
        "@keyframes wave{from{transform:translateX(0)}to{transform:translateX(-120px)}}.wv{animation:wave 9s linear infinite}"
        "@keyframes bob{0%,100%{transform:translateY(0)}50%{transform:translateY(2px)}}.bob{animation:bob 4s ease-in-out infinite}"
        "@media (prefers-reduced-motion:reduce){*{animation:none!important}}"
    )

    g = [f'<g clip-path="url(#frame)">', f'<rect width="{W}" height="{HZ}" fill="url(#sky)"/>']
    # stars
    for i in range(70):
        x, y = rng.uniform(10, W - 10), rng.uniform(8, HZ - 40) ** 1.0
        if (x - SX) ** 2 + (y - HZ) ** 2 < (SR + 40) ** 2 or (x > 820 and y < 58):
            continue
        sz = rng.choice([1.5, 2, 2, 2, 3])
        col = rng.choice([C["cream"], C["cream"], C["gold"], "#C9C2FF"])
        op = 0.25 + 0.75 * (1 - y / HZ)
        tw = rng.random() < 0.55
        style = f' style="animation-delay:-{rng.uniform(0, 3.2):.2f}s;animation-duration:{rng.uniform(2.4, 5.2):.2f}s"' if tw else ""
        g.append(f'<rect x="{n(x)}" y="{n(y)}" width="{sz}" height="{sz}" fill="{col}" opacity="{n(op)}"'
                 + (f' class="tw"{style}' if tw else "") + "/>")
    # shooting star
    g.append('<g class="shoot"><rect x="560" y="46" width="70" height="1.6" rx=".8" fill="url(#streak)" transform="rotate(-21.8 630 47)"/></g>')
    # sun + glow
    g.append(f'<circle class="glow" cx="{SX}" cy="{HZ}" r="230" fill="url(#glow)"/>')
    g.append(f'<rect width="{W}" height="{HZ}" fill="url(#sun)" mask="url(#sunm)" transform="translate(0 0)"/>')
    # we need the gradient to span the sun only: draw a sun-sized rect under mask
    g[-1] = f'<rect x="{SX - SR}" y="{HZ - SR}" width="{SR * 2}" height="{SR}" fill="url(#sun)" mask="url(#sunm)"/>'
    # sea
    g.append(f'<rect y="{HZ}" width="{W}" height="{H - HZ}" fill="url(#sea)"/>')
    g.append(f'<rect y="{HZ - 1}" width="{W}" height="1.6" fill="url(#hz)"/>')
    # sun reflection
    for i in range(10):
        yy = HZ + 7 + i * 10.5
        w = (SR * 1.7) * (1 - i * 0.075) * rng.uniform(0.82, 1.05)
        col = [C["gold"], C["saffron"], C["saffron"], C["coral"], C["coral"], C["rose"]][min(i // 2, 5)]
        op = 0.85 - i * 0.07
        dly = rng.uniform(0, 3.6)
        segs = rng.choice([1, 2, 2, 3])
        x0 = SX - w / 2
        sw = w / segs
        for j in range(segs):
            g.append(f'<rect class="rf" style="animation-delay:-{dly + j * .4:.2f}s" x="{n(x0 + j * sw + 3)}" y="{n(yy)}" '
                     f'width="{n(sw - 6)}" height="{n(2 + i * 0.25)}" rx="1" fill="{col}" opacity="{n(op)}"/>')
    # faint waves across the sea
    wv = []
    for i in range(16):
        yy = HZ + 14 + rng.uniform(0, H - HZ - 30)
        xx = rng.uniform(0, W)
        wv.append(f'<rect x="{n(xx)}" y="{n(yy)}" width="{n(rng.uniform(14, 46))}" height="1.2" fill="{C["teal"]}" opacity="{n(rng.uniform(.12, .3))}"/>')
    g.append(f'<g class="wv">{"".join(wv)}<g transform="translate(120 0)">{"".join(wv)}</g></g>')
    # fishing boat on the horizon
    boat = ["......#......", "......##.....", "......###....", "......####...", "......#####..", "......#......", "#############", ".###########.", "..#########.."]
    g.append(f'<g class="bob"><path d="{cells_path(bitmap_cells(boat), 2.2, 618, HZ - 19.5)}" fill="{C["palm"]}"/></g>')

    # land + palms
    P = 5
    land = set()
    for gx in range(int(560 / P), int(W / P) + 2):
        x = gx * P
        t = min(1, max(0, (x - 560) / 300))
        top = 400 - (16 + 34 * (3 * t * t - 2 * t * t * t)) + 3 * math.sin(x / 37)
        for gy in range(int(top / P), int(H / P) + 1):
            land.add((gx, gy))
    g.append(f'<path d="{cells_path(land, P)}" fill="{C["palm"]}"/>')
    rim = {(gx, gy) for gx, gy in land if (gx, gy - 1) not in land}
    g.append(f'<path d="{cells_path(rim, P)}" fill="{C["coral"]}" opacity=".28"/>')
    t1, f1, n1 = palm_cells(930, 370, 892, 128, P, 100, -26, [156, 190, 226, 262, 302, 338, 16], random.Random(3))
    t2, f2, n2 = palm_cells(712, 386, 742, 214, P, 62, 16, [162, 198, 240, 292, 334, 14], random.Random(11))
    g.append(f'<path d="{cells_path(t2, P)}" fill="{C["palm"]}"/>')
    g.append(f'<g style="transform-origin:742px 214px;animation:sway2 6.5s ease-in-out infinite">'
             f'<path d="{cells_path(f2 | n2, P)}" fill="{C["palm"]}"/></g>')
    g.append(f'<path d="{cells_path(t1, P)}" fill="{C["palm"]}"/>')
    g.append(f'<g style="transform-origin:892px 128px;animation:sway 5.5s ease-in-out infinite">'
             f'<path d="{cells_path(f1 | n1, P)}" fill="{C["palm"]}"/></g>')

    # CRT scanlines + vignette sit under the type so the name stays crisp
    g.append(f'<rect width="{W}" height="{H}" fill="url(#scan)"/>')
    g.append(f'<rect width="{W}" height="{H}" fill="url(#vig)"/>')
    # legibility shade + text
    g.append(f'<rect width="{W}" height="{H}" fill="url(#shade)"/>')
    X = 56
    g.append(f'<rect x="{X}" y="64" width="8" height="8" fill="{C["saffron"]}" transform="rotate(45 {X + 4} 68)"/>')
    g.append(s.text(X + 20, 74, CONFIG["kicker"], "jb7", 14, C["saffron"], ls=2.6))
    g.append(s.text(W - 40, 44, CONFIG["coords"], "jb4", 12.5, C["muted"], anchor="end", ls=1.5, extra='opacity=".7"'))

    name_font = Font.get("sg7")
    size = 64
    while name_font.width(CONFIG["name"], size, -1.5) > 560:
        size -= 1
    g.append(s.text(X - 3, 148, CONFIG["name"], "sg7", size, C["cream"], ls=-1.5))
    g.append(s.text(X, 192, CONFIG["alias"], "is", 36, C["saffron"]))

    # typewriter
    TY, TS = 246, 19
    cw = Font.get("jb4").width("M", TS)
    tx = X + cw * 2
    total, lines_anim, (ckt, cvals) = typing_timeline(CONFIG["typing"], cw)
    g.append(s.text(X, TY, ">", "jb7", TS, C["teal"]))
    for i, (line, (kt, vals)) in enumerate(zip(CONFIG["typing"], lines_anim)):
        s.defs.append(
            f'<clipPath id="ty{i}"><rect x="{n(tx)}" y="{TY - TS}" width="0" height="{TS + 6}">'
            f'<animate attributeName="width" dur="{n(total)}s" repeatCount="indefinite" calcMode="discrete" keyTimes="{kt}" values="{vals}"/>'
            f"</rect></clipPath>"
        )
        g.append(f'<g clip-path="url(#ty{i})">{s.text(tx, TY, line, "jb4", TS, C["cream"])}</g>')
    cx_vals = ";".join(n(tx + float(v) + 2) for v in cvals.split(";"))
    g.append(
        f'<rect class="blink" x="{n(tx + 2)}" y="{TY - TS + 3}" width="{n(cw * 0.55)}" height="{TS}" fill="{C["saffron"]}">'
        f'<animate attributeName="x" dur="{n(total)}s" repeatCount="indefinite" calcMode="discrete" keyTimes="{ckt}" values="{cx_vals}"/></rect>'
    )

    # game HUD
    HY = 352
    hearts = "".join(
        f'<path d="{cells_path(bitmap_cells(HEART), 2.3, X + i * 21, HY - 14)}" fill="{C["coral"]}"/>' for i in range(3)
    )
    g.append(hearts)
    hx = X + 3 * 21 + 14
    hud = s.tspan_text(hx, HY, [
        ("P1 ATISH", "px", 14, C["cream"], 0),
        ("CLASS: FOUNDER", "px", 14, C["muted"], 20),
        ("ZONE: GOA", "px", 14, C["muted"], 20),
    ], extra='letter-spacing="1"')
    g.append(hud)
    pw = Font.get("px")
    hud_w = pw.width("P1 ATISH", 14, 1) + pw.width("CLASS: FOUNDER", 14, 1) + pw.width("ZONE: GOA", 14, 1) + 40 + 18
    g.append(s.text(hx + hud_w + 22, HY, "PRESS START", "px", 14, C["saffron"], ls=1, cls="blink"))
    g.append("</g>")
    g.append(f'<rect x=".5" y=".5" width="{W - 1}" height="{H - 1}" rx="21.5" stroke="#FFFFFF" stroke-opacity=".08"/>')
    s.body += g
    write("hero.svg", s)


# ════════════════════════════════════════════════════════════════════
#  BUTTONS
# ════════════════════════════════════════════════════════════════════
def build_buttons():
    f = Font.get("jb7")
    for slug, label in CONFIG["buttons"]:
        txt = label.upper()
        tw = f.width(txt, 12.5, 2)
        W, H = int(tw + 30 + 24 + 22), 46
        s = Svg(W, H, label)
        s.css.append("@keyframes p{0%,100%{opacity:.35}50%{opacity:1}}.p{animation:p 2.4s ease-in-out infinite}")
        s.add(f'<rect x=".75" y=".75" width="{W - 1.5}" height="{H - 1.5}" rx="{H / 2 - .75}" fill="{C["ink2"]}" stroke="{C["line"]}" stroke-width="1.5"/>')
        s.add(f'<rect class="p" x="20" y="{H / 2 - 3}" width="6" height="6" fill="{C["saffron"]}"/>')
        s.add(s.text(36, H / 2 + 4.5, txt, "jb7", 12.5, C["cream"], ls=2))
        s.add(arrow(36 + tw + 12, H / 2 - 5, 10, C["saffron"]))
        write(f"btn-{slug}.svg", s)


# ════════════════════════════════════════════════════════════════════
#  SECTION HEADS (dark + light)
# ════════════════════════════════════════════════════════════════════
SECTIONS = [
    ("ventures", "01", "Ventures", "WHAT I'M BUILDING"),
    ("work", "02", "Selected work", "OPEN SOURCE"),
    ("toolkit", "03", "Toolkit", "WHAT I REACH FOR"),
    ("momentum", "04", "Momentum", "BUILDING IN PUBLIC"),
]


def build_heads():
    for slug, num, title, note in SECTIONS:
        for mode in ("dark", "light"):
            ink = C["cream"] if mode == "dark" else "#15162B"
            acc = C["saffron"] if mode == "dark" else "#C2410C"
            rule = C["line"] if mode == "dark" else "#D6D8E7"
            mut = C["muted"] if mode == "dark" else "#5A5D7A"
            W, H = 1000, 64
            s = Svg(W, H, f"{num} — {title}")
            s.add(s.text(4, 42, num, "jb7", 15, acc, ls=1))
            s.add(f'<rect x="32" y="33" width="14" height="2" fill="{acc}"/>')
            s.add(s.text(58, 44, title, "sg7", 28, ink, ls=-.5))
            tw = Font.get("sg7").width(title, 28, -.5)
            nw = Font.get("jb4").width(note, 12.5, 2)
            x1, x2 = 58 + tw + 22, W - 4 - nw - 18
            s.add(f'<rect x="{n(x1)}" y="36" width="{n(x2 - x1)}" height="1" fill="{rule}"/>')
            for i in range(3):
                s.add(f'<rect x="{n(x2 - 4 - i * 7)}" y="34" width="4" height="4" fill="{acc}" opacity="{n(1 - i * .3)}"/>')
            s.add(s.text(W - 4, 41, note, "jb4", 12.5, mut, anchor="end", ls=2))
            write(f"head-{slug}-{mode}.svg", s)


# ════════════════════════════════════════════════════════════════════
#  VENTURE CARDS
# ════════════════════════════════════════════════════════════════════
def card_shell(s: Svg, W, H, top, bottom, border):
    s.defs.append(f'<linearGradient id="bg" x1="0" y1="0" x2="1" y2="1"><stop offset="0" stop-color="{top}"/><stop offset="1" stop-color="{bottom}"/></linearGradient>')
    s.defs.append(f'<clipPath id="cf"><rect width="{W}" height="{H}" rx="18"/></clipPath>')
    s.defs.append('<pattern id="dots" width="14" height="14" patternUnits="userSpaceOnUse"><rect width="1.4" height="1.4" fill="#fff" opacity=".07"/></pattern>')
    s.add(f'<g clip-path="url(#cf)"><rect width="{W}" height="{H}" fill="url(#bg)"/><rect width="{W}" height="{H}" fill="url(#dots)"/>')


def chips(s: Svg, x, y, items, fg, bd, size=12):
    f = Font.get("jb7")
    out = []
    for it in items:
        w = f.width(it, size, 1.2) + 20
        out.append(f'<rect x="{n(x)}" y="{n(y)}" width="{n(w)}" height="27" rx="13.5" fill="#FFFFFF" fill-opacity=".03" stroke="{bd}"/>')
        out.append(s.text(x + 10, y + 18, it, "jb7", size, fg, ls=1.2))
        x += w + 8
    return "".join(out), x


def build_venture_datatree():
    v = CONFIG["ventures"]["datatree"]
    W, H = 490, 300
    s = Svg(W, H, "DataTree Studios — game studio, Goa", "Founder of DataTree Studios, an indie game studio in Goa.")
    s.css.append(
        "@keyframes lit{0%,100%{opacity:.35}12%{opacity:1}30%{opacity:.35}}.nd{animation:lit 4s ease-out infinite}"
        "@keyframes flow{to{stroke-dashoffset:-24}}.ed{animation:flow 1.6s linear infinite}"
        "@keyframes fall{0%{transform:translateY(0);opacity:0}15%{opacity:1}100%{transform:translateY(46px);opacity:0}}.lf{animation:fall 5s ease-in infinite}"
        "@keyframes p{0%,100%{opacity:.35}50%{opacity:1}}.p{animation:p 2.4s ease-in-out infinite}"
        "@media (prefers-reduced-motion:reduce){*{animation:none!important}}"
    )
    card_shell(s, W, H, "#10182A", "#0B1A1D", "#23413A")
    LEAF, EDGE = C["leaf"], "#2F6B52"
    s.add(f'<rect x="28" y="32" width="7" height="7" fill="{LEAF}"/>')
    s.add(s.text(44, 40.5, v["kicker"], "jb7", 13, LEAF, ls=2))
    s.add(s.text(26, 96, v["title"][0], "sg7", 40, C["cream"], ls=-1))
    s.add(s.text(26, 138, v["title"][1], "sg5", 40, C["muted"], ls=-1))
    s.add(s.text(28, 182, v["tagline"], "is", 22, C["cream"]))

    # binary "data tree": root at bottom, leaves at top, orthogonal pixel edges
    ox, oy = 386, 0
    levels = [(170, [386]), (132, [340, 432]), (96, [316, 364, 408, 456]), (60, [304, 328, 352, 376, 396, 420, 444, 468])]
    edges, nodes = [], []
    s.add(f'<rect x="{ox - 3}" y="170" width="6" height="18" fill="{EDGE}"/>')
    s.add(f'<rect x="{ox - 16}" y="186" width="32" height="4" fill="{EDGE}"/>')
    for li in range(1, len(levels)):
        py, pxs = levels[li - 1]
        cy, cxs = levels[li]
        for ci, cx in enumerate(cxs):
            px = pxs[ci // 2]
            midy = (py + cy) / 2
            edges.append(f"M{px} {py}V{midy}H{cx}V{cy}")
    s.add(f'<path d="{"".join(edges)}" stroke="{EDGE}" stroke-width="2.5" stroke-linecap="square"/>')
    s.add(f'<path class="ed" d="{"".join(edges)}" stroke="{LEAF}" stroke-width="2.5" stroke-dasharray="3 9" stroke-linecap="square" opacity=".9" style="animation-direction:reverse"/>')
    for li, (yy, xs) in enumerate(levels):
        sz = [14, 10, 9, 10][li]
        for xi, xx in enumerate(xs):
            delay = (3 - li) * 0.32 + xi * 0.05
            col = LEAF if li == 3 else ("#BFF5BF" if li == 0 else "#5FBF7A")
            nodes.append(f'<rect x="{n(xx - sz / 2)}" y="{n(yy - sz / 2)}" width="{sz}" height="{sz}" fill="{C["ink2"]}" stroke="{EDGE}" stroke-width="1.5"/>')
            nodes.append(f'<rect class="nd" style="animation-delay:{delay:.2f}s" x="{n(xx - sz / 2 + 2)}" y="{n(yy - sz / 2 + 2)}" width="{sz - 4}" height="{sz - 4}" fill="{col}"/>')
    s.add("".join(nodes))
    rng = random.Random(5)
    for i, xx in enumerate([304, 352, 420, 468, 376]):
        s.add(f'<rect class="lf" style="animation-delay:{i * 1.05 + rng.uniform(0, .5):.2f}s" x="{xx - 1.5}" y="68" width="3" height="3" fill="{LEAF}"/>')
    s.add(s.text(466, 214, v["caption"], "jb4", 12, C["dim"], anchor="end", ls=.3))

    cs, _ = chips(s, 26, 232, v["chips"], C["cream"], "#2C4B45")
    s.add(cs)
    s.add(f'<rect x="26" y="{H - 30}" width="{W - 52}" height="1" fill="#FFFFFF" opacity=".07"/>')
    s.add(s.text(26, H - 11, "FOUNDER", "jb7", 10.5, C["muted"], ls=2))
    s.add(f'<rect class="p" x="{W - 26 - Font.get("jb7").width(v["footer_right"], 10.5, 2) - 14}" y="{H - 19}" width="6" height="6" fill="{LEAF}"/>')
    s.add(s.text(W - 26, H - 11, v["footer_right"], "jb7", 10.5, LEAF, anchor="end", ls=2))
    s.add("</g>")
    s.add(f'<rect x=".75" y=".75" width="{W - 1.5}" height="{H - 1.5}" rx="17.25" stroke="#23413A" stroke-width="1.5"/>')
    write("venture-datatree.svg", s)


def build_venture_booleanchitra():
    v = CONFIG["ventures"]["booleanchitra"]
    W, H = 490, 300
    s = Svg(W, H, "BooleanChitra — AI software agency, Goa", "Founder of BooleanChitra, an AI software agency building AI agents and automation.")
    s.css.append(
        "@keyframes rip{0%,100%{opacity:.35}50%{opacity:1}}.on{animation:rip 3s ease-in-out infinite}"
        "@keyframes flip{0%,92%,100%{opacity:.3}95%{opacity:.9}}.fl{animation:flip 7s linear infinite}"
        "@media (prefers-reduced-motion:reduce){*{animation:none!important}}"
    )
    card_shell(s, W, H, "#16122C", "#1F1222", "#4A2A3A")
    s.add(f'<rect x="28" y="32" width="7" height="7" fill="{C["saffron"]}"/>')
    s.add(s.text(44, 40.5, v["kicker"], "jb7", 13, C["saffron"], ls=2))
    s.add(s.text(26, 96, v["title"][0], "sg7", 40, C["cream"], ls=-1))
    s.add(s.text(28, 140, v["title"][1], "is", 48, C["saffron"]))
    s.add(s.text(28, 182, v["tagline"], "is", 21, C["cream"]))

    # a picture (chitra) drawn with booleans: a 4-point spark made of 1s on a field of 0s
    N, cell = 13, 11.6
    gx0, gy0 = 320, 36
    r = (N - 1) / 2
    rng = random.Random(2)
    out = []
    for j in range(N):
        for i in range(N):
            u, w = abs(i - r), abs(j - r)
            on = (u ** 0.72 + w ** 0.72) <= r ** 0.72 + 0.05
            small = (abs(i - 10) + abs(j - 2)) <= 1
            x, y = gx0 + i * cell, gy0 + j * cell + 9
            if on or small:
                d = math.hypot(i - r, j - r)
                col = C["gold"] if d < 1.6 else (C["saffron"] if d < 3.6 else C["coral"])
                out.append(s.text(x, y, "1", "jb7", 11, col, cls="on", extra=f'style="animation-delay:-{3 - d * .35:.2f}s"'))
            else:
                flick = rng.random() < 0.07
                out.append(s.text(x, y, "0", "jb4", 11, "#5B4767", cls="fl" if flick else "",
                                  extra=(f'style="animation-delay:-{rng.uniform(0, 7):.2f}s"' if flick else 'opacity=".3"')))
    s.add(f'<g text-anchor="middle">{"".join(out)}</g>')
    s.add(s.text(466, 214, v["caption"], "jb4", 12, C["dim"], anchor="end", ls=.3))

    cs, _ = chips(s, 26, 232, v["chips"], C["cream"], "#4A2F45")
    s.add(cs)
    s.add(f'<rect x="26" y="{H - 30}" width="{W - 52}" height="1" fill="#FFFFFF" opacity=".07"/>')
    s.add(s.text(26, H - 11, "FOUNDER", "jb7", 10.5, C["muted"], ls=2))
    fw = Font.get("jb7").width(v["footer_right"], 10.5, 2)
    s.add(s.text(W - 44, H - 11, v["footer_right"], "jb7", 10.5, C["saffron"], anchor="end", ls=2))
    s.add(arrow(W - 38, H - 20, 9, C["saffron"], 1.5))
    s.add("</g>")
    s.add(f'<rect x=".75" y=".75" width="{W - 1.5}" height="{H - 1.5}" rx="17.25" stroke="#4A2A3A" stroke-width="1.5"/>')
    write("venture-booleanchitra.svg", s)


# ════════════════════════════════════════════════════════════════════
#  PROJECT CARDS
# ════════════════════════════════════════════════════════════════════
def wrap(text, font: Font, size, maxw, maxlines=2):
    words, lines, cur = text.split(), [], ""
    for wd in words:
        t = (cur + " " + wd).strip()
        if font.width(t, size) <= maxw:
            cur = t
        else:
            lines.append(cur)
            cur = wd
    lines.append(cur)
    if len(lines) > maxlines:
        lines = lines[:maxlines]
        while font.width(lines[-1] + "…", size) > maxw:
            lines[-1] = lines[-1].rsplit(" ", 1)[0]
        lines[-1] += "…"
    return lines


def build_projects():
    for idx, p in enumerate(CONFIG["projects"], 1):
        W, H = 490, 184
        lang, lcol = p["lang"]
        s = Svg(W, H, f'{p["name"]} — {p["desc"]}')
        s.defs.append(f'<linearGradient id="tl" x1="0" y1="0" x2="1" y2="0"><stop offset="0" stop-color="{lcol}"/><stop offset=".6" stop-color="{lcol}" stop-opacity="0"/></linearGradient>')
        s.defs.append(f'<clipPath id="cf"><rect width="{W}" height="{H}" rx="16"/></clipPath>')
        s.defs.append('<pattern id="dots" width="14" height="14" patternUnits="userSpaceOnUse"><rect width="1.4" height="1.4" fill="#fff" opacity=".06"/></pattern>')
        s.add(f'<g clip-path="url(#cf)"><rect width="{W}" height="{H}" fill="{C["ink2"]}"/><rect width="{W}" height="{H}" fill="url(#dots)"/>')
        s.add(s.text(W - 22, H - 14, f"{idx:02d}", "px", 54, C["cream"], anchor="end", extra='opacity=".05"'))
        s.add(f'<rect width="{W}" height="2" fill="url(#tl)"/>')
        s.add(f'<circle cx="31" cy="33" r="5" fill="{lcol}"/>')
        s.add(s.text(44, 38, lang, "jb4", 13, C["muted"], ls=.3))
        s.add(f'<circle cx="{W - 34}" cy="33" r="14" stroke="{C["line"]}" stroke-width="1.2"/>')
        s.add(arrow(W - 38.5, 28.5, 9, C["saffron"], 1.6))
        name = p["name"]
        size = 25
        while Font.get("sg7").width(name, size, -.4) > W - 52:
            size -= .5
        s.add(s.text(26, 84, name, "sg7", size, C["cream"], ls=-.4))
        for i, line in enumerate(wrap(p["desc"], Font.get("sg4"), 16, W - 52)):
            s.add(s.text(26, 113 + i * 22, line, "sg4", 16, C["muted"]))
        s.add(s.text(26, H - 18, p["tags"], "jb7", 12, C["saffron"], ls=1.4, extra='opacity=".85"'))
        s.add("</g>")
        s.add(f'<rect x=".75" y=".75" width="{W - 1.5}" height="{H - 1.5}" rx="15.25" stroke="{C["line"]}" stroke-width="1.5"/>')
        write(f'project-{p["slug"]}.svg', s)


# ════════════════════════════════════════════════════════════════════
#  TOOLKIT
# ════════════════════════════════════════════════════════════════════
def build_toolkit():
    rows = CONFIG["toolkit"]
    W, RH = 1000, 50
    H = 30 + (len(rows) - 1) * RH + 35 + 30
    s = Svg(W, H, "Toolkit: " + "; ".join(f"{r[0]}: {', '.join(r[2])}" for r in rows))
    s.defs.append(f'<clipPath id="cf"><rect width="{W}" height="{H}" rx="18"/></clipPath>')
    s.defs.append('<pattern id="dots" width="14" height="14" patternUnits="userSpaceOnUse"><rect width="1.4" height="1.4" fill="#fff" opacity=".06"/></pattern>')
    s.add(f'<g clip-path="url(#cf)"><rect width="{W}" height="{H}" fill="{C["ink2"]}"/><rect width="{W}" height="{H}" fill="url(#dots)"/>')
    f5, fj = Font.get("sg5"), Font.get("jb7")
    y = 30
    for label, acc, items in rows:
        col = C[acc]
        s.add(f'<rect x="32" y="{y + 13}" width="7" height="7" fill="{col}"/>')
        s.add(s.text(48, y + 22, label, "jb7", 12.5, C["muted"], ls=2))
        x = 200
        for it in items:
            w = f5.width(it, 16) + 36
            s.add(f'<rect x="{n(x)}" y="{y}" width="{n(w)}" height="35" rx="10" fill="{C["chip"]}" stroke="{C["line"]}"/>')
            s.add(f'<rect x="{n(x + 13)}" y="{y + 14}" width="7" height="7" fill="{col}" opacity=".9"/>')
            s.add(s.text(x + 27, y + 23, it, "sg5", 16, C["cream"]))
            x += w + 10
        y += RH
    s.add("</g>")
    s.add(f'<rect x=".75" y=".75" width="{W - 1.5}" height="{H - 1.5}" rx="17.25" stroke="{C["line"]}" stroke-width="1.5"/>')
    write("toolkit.svg", s)


# ════════════════════════════════════════════════════════════════════
#  STATS (seed or live)
# ════════════════════════════════════════════════════════════════════
GQL = """
query($login: String!) {
  user(login: $login) {
    all: repositories(ownerAffiliations: OWNER, privacy: PUBLIC) { totalCount }
    own: repositories(ownerAffiliations: OWNER, privacy: PUBLIC, isFork: false, first: 100) {
      nodes { languages(first: 10, orderBy: {field: SIZE, direction: DESC}) { edges { size node { name color } } } }
    }
    contributionsCollection {
      contributionCalendar { totalContributions weeks { contributionDays { date contributionCount } } }
    }
  }
}"""


def fetch_live(username: str) -> dict:
    token = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")
    if not token:
        sys.exit("--live needs GITHUB_TOKEN")
    req = urllib.request.Request(
        "https://api.github.com/graphql",
        data=json.dumps({"query": GQL, "variables": {"login": username}}).encode(),
        headers={"Authorization": f"bearer {token}", "Content-Type": "application/json", "User-Agent": "profile-art"},
    )
    with urllib.request.urlopen(req, timeout=30) as r:
        data = json.load(r)
    if "errors" in data:
        sys.exit(f"GraphQL error: {data['errors']}")
    u = data["data"]["user"]
    cal = u["contributionsCollection"]["contributionCalendar"]
    days = sorted((d["date"], d["contributionCount"]) for w in cal["weeks"] for d in w["contributionDays"])
    longest = run = 0
    for _, c in days:
        run = run + 1 if c > 0 else 0
        longest = max(longest, run)
    cur = 0
    seq = [c for _, c in days]
    if seq and seq[-1] == 0:  # today not committed yet → don't break the streak
        seq = seq[:-1]
    for c in reversed(seq):
        if c == 0:
            break
        cur += 1
    langs = defaultdict(lambda: [0, "#888888"])
    for node in u["own"]["nodes"]:
        for e in node["languages"]["edges"]:
            langs[e["node"]["name"]][0] += e["size"]
            langs[e["node"]["name"]][1] = e["node"]["color"] or "#888888"
    top = sorted(langs.items(), key=lambda kv: -kv[1][0])
    return {
        "contributions": cal["totalContributions"],
        "current_streak": cur,
        "longest_streak": longest,
        "repos": u["all"]["totalCount"],
        "languages": [(k, v[1], v[0]) for k, v in top],
        "languages_basis": "by bytes of code",
    }


def build_stats(st: dict):
    W, H = 1000, 284
    stamp = datetime.now(timezone.utc).strftime("%d %b %Y")
    payload = json.dumps({k: st[k] for k in sorted(st)}, sort_keys=True, default=str)
    digest = hashlib.sha1(payload.encode() + Path(__file__).read_bytes()).hexdigest()[:12]  # data + layout
    out = ASSETS / "stats.svg"
    if out.exists() and f'data-hash="{digest}"' in out.read_text(encoding="utf-8"):
        print("  · stats.svg                          unchanged")
        return

    def fmt(v):
        return "—" if v is None else f"{v:,}"

    s = Svg(W, H, (f'GitHub momentum: {fmt(st["contributions"])} contributions in the last year, '
                   f'current streak {fmt(st["current_streak"])} days, longest streak {fmt(st["longest_streak"])} days, '
                   f'{fmt(st["repos"])} public repositories.'))
    s.meta = f'<metadata data-hash="{digest}"/>'
    s.css.append("@keyframes p{0%,100%{opacity:.35}50%{opacity:1}}.p{animation:p 2.4s ease-in-out infinite}"
                 "@media (prefers-reduced-motion:reduce){*{animation:none!important}}")
    s.defs.append(f'<clipPath id="cf"><rect width="{W}" height="{H}" rx="18"/></clipPath>')
    s.defs.append('<pattern id="dots" width="14" height="14" patternUnits="userSpaceOnUse"><rect width="1.4" height="1.4" fill="#fff" opacity=".06"/></pattern>')
    s.add(f'<g clip-path="url(#cf)"><rect width="{W}" height="{H}" fill="{C["ink2"]}"/><rect width="{W}" height="{H}" fill="url(#dots)"/>')
    s.add(f'<rect class="p" x="32" y="30" width="7" height="7" fill="{C["teal"]}"/>')
    s.add(s.text(48, 38, "LIVE FROM GITHUB", "jb7", 12.5, C["teal"], ls=2))
    s.add(s.text(W - 32, 37.5, f"UPDATED {stamp.upper()}", "jb4", 12, C["dim"], anchor="end", ls=1.5))

    tiles = [
        ("Contributions", fmt(st["contributions"]), "last 12 months"),
        ("Current streak", fmt(st["current_streak"]), "days in a row"),
        ("Longest streak", fmt(st["longest_streak"]), "days, last 12 months"),
        ("Public repos", fmt(st["repos"]), "and counting"),
    ]
    tw = (W - 64) / 4
    for i, (label, val, sub) in enumerate(tiles):
        x = 32 + i * tw
        if i:
            s.add(f'<rect x="{n(x - 1)}" y="64" width="1" height="92" fill="{C["line"]}"/>')
        px = x + (0 if i == 0 else 24)
        s.add(s.text(px, 82, label, "sg5", 15.5, C["muted"]))
        s.add(s.text(px - 2, 132, val, "sg7", 48, C["cream"], ls=-1.5))
        s.add(s.text(px, 154, sub, "jb4", 12, C["dim"], ls=.2))

    # top languages: one segmented bar + legend
    langs = [l for l in st["languages"] if l[2] > 0]
    total = sum(l[2] for l in langs) or 1
    top = langs[:5]
    other = total - sum(l[2] for l in top)
    if other > 0:
        top.append(("Other", "#5C5F85", other))
    s.add(s.text(32, 196, "Top languages", "sg5", 15.5, C["muted"]))
    s.add(s.text(W - 32, 196, st.get("languages_basis", ""), "jb4", 12, C["dim"], anchor="end", ls=.3))
    bx, bw, by = 32, W - 64, 210
    gap = 2
    usable = bw - gap * (len(top) - 1)
    s.defs.append(f'<clipPath id="bar"><rect x="{bx}" y="{by}" width="{bw}" height="10" rx="4"/></clipPath>')
    segs, x = [], bx
    for name, col, v in top:
        w = usable * v / total
        segs.append(f'<rect x="{n(x)}" y="{by}" width="{n(max(w, 1))}" height="10" fill="{col}"/>')
        x += w + gap
    s.add(f'<g clip-path="url(#bar)">{"".join(segs)}</g>')
    lx, fj = 32, Font.get("jb4")
    for name, col, v in top:
        label = f"{name} {v / total * 100:.0f}%"
        s.add(f'<rect x="{n(lx)}" y="242" width="9" height="9" rx="2" fill="{col}"/>')
        s.add(s.text(lx + 16, 251, label, "jb4", 12.5, C["muted"]))
        lx += fj.width(label, 12.5) + 34
    s.add("</g>")
    s.add(f'<rect x=".75" y=".75" width="{W - 1.5}" height="{H - 1.5}" rx="17.25" stroke="{C["line"]}" stroke-width="1.5"/>')
    write("stats.svg", s)


# ════════════════════════════════════════════════════════════════════
#  FOOTER
# ════════════════════════════════════════════════════════════════════
def build_footer():
    W, H = 1000, 210
    s = Svg(W, H, CONFIG["footer_line"] + " — " + CONFIG["footer_sub"].title())
    s.defs += [
        f'<clipPath id="cf"><rect width="{W}" height="{H}" rx="22"/></clipPath>',
        '<linearGradient id="fb" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#0E1022"/><stop offset="1" stop-color="#1A1030"/></linearGradient>',
        '<radialGradient id="fs"><stop offset="0" stop-color="#FF9933" stop-opacity=".45"/><stop offset="1" stop-color="#FF5E62" stop-opacity="0"/></radialGradient>',
        '<linearGradient id="sunf" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#FFC86B"/><stop offset=".6" stop-color="#FF9933"/><stop offset="1" stop-color="#FF5E62"/></linearGradient>',
    ]
    s.css.append(
        "@keyframes w1{from{transform:translateX(0)}to{transform:translateX(-200px)}}"
        ".w1{animation:w1 7s linear infinite}.w2{animation:w1 11s linear infinite reverse}.w3{animation:w1 16s linear infinite}"
        "@media (prefers-reduced-motion:reduce){*{animation:none!important}}"
    )
    s.add(f'<g clip-path="url(#cf)"><rect width="{W}" height="{H}" fill="url(#fb)"/>')
    # pixel sun sinking behind the waves
    P = 6
    sun = {(i, j) for i in range(-8, 9) for j in range(-8, 1) if i * i + j * j <= 64}
    s.add(f'<circle cx="500" cy="172" r="110" fill="url(#fs)"/>')
    s.add(f'<path d="{cells_path(sun, P, 500 - 3, 172)}" fill="url(#sunf)"/>')

    def wave_path(y, amp, wl, w=W + 400):
        d = f"M-200 {y}"
        x = -200
        while x < w:
            d += f" q{wl / 4} {-amp} {wl / 2} 0 t{wl / 2} 0"
            x += wl
        return d + f" V{H} H-200 Z"

    s.add(f'<path class="w3" d="{wave_path(150, 6, 200)}" fill="#2EC4B6" opacity=".10"/>')
    s.add(f'<path class="w2" d="{wave_path(164, 7, 200)}" fill="#1D2A55" opacity=".95"/>')
    s.add(f'<path class="w1" d="{wave_path(180, 6, 200)}" fill="#0E1022"/>')
    s.add(s.text(W / 2, 66, CONFIG["footer_line"], "is", 34, C["cream"], anchor="middle"))
    s.add(s.text(W / 2, 100, CONFIG["footer_sub"], "jb4", 12.5, C["muted"], anchor="middle", ls=2.2))
    s.add("</g>")
    s.add(f'<rect x=".5" y=".5" width="{W - 1}" height="{H - 1}" rx="21.5" stroke="#FFFFFF" stroke-opacity=".08"/>')
    write("footer.svg", s)


# ════════════════════════════════════════════════════════════════════
def main():
    ASSETS.mkdir(exist_ok=True)
    live = "--live" in sys.argv
    only_stats = "--stats-only" in sys.argv
    print(f"Building profile art → {ASSETS.relative_to(ROOT)}/")
    stats = fetch_live(CONFIG["username"]) if live else CONFIG["seed_stats"]
    if not only_stats:
        build_hero()
        build_buttons()
        build_heads()
        build_venture_datatree()
        build_venture_booleanchitra()
        build_projects()
        build_toolkit()
        build_footer()
    build_stats(stats)
    print("done.")


if __name__ == "__main__":
    main()
