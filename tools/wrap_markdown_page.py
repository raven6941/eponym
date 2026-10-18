#!/usr/bin/env python3
"""Wrap Pandoc HTML in the site's shared notebook layout."""
from html import escape
from pathlib import Path
import re
import sys

source, fragment, destination = map(Path, sys.argv[1:4])
output_root = Path(sys.argv[4]) if len(sys.argv) > 4 else Path(".")
title = source.stem.replace("_", " ").replace("-", " ").title()
content = fragment.read_text()
# GitHub renders source links as Markdown; generated Pages links use HTML.
content = re.sub(r'(href="[^"#?]+)\.md([#?][^"]*)?"', r'\1.html\2"', content)
depth = len(source.parent.parts)
root_prefix = "../" * depth
is_home = source.as_posix() == "README.md"
if is_home:
    root_prefix = ""
    slug_counts = {}

    def add_anchor(match):
        heading_depth, label = match.group(1), match.group(2)
        plain = re.sub(r"<[^>]+>", "", label)
        base = re.sub(r"[^a-z0-9]+", "-", plain.lower()).strip("-")
        count = slug_counts.get(base, 0)
        slug_counts[base] = count + 1
        anchor = f"{base}-{count}" if count else base
        return f'<h{heading_depth} id="{anchor}">{label}</h{heading_depth}>'

    content = re.sub(r'<h([23])>(.*?)</h[23]>', add_anchor, content, flags=re.S)
    heading_rows = re.findall(r'<h([23]) id="([^"]+)">(.*?)</h[23]>', content, re.S)
    links = "".join(
        '<a class="{}" href="#{}">{}</a>'.format(
            "subheading" if level == "3" else "", anchor,
            re.sub(r"<[^>]+>", "", label))
        for level, anchor, label in heading_rows
    )
    aside = f'<aside aria-label="Table of contents"><p class="index-label">On this page</p><nav>{links}</nav></aside>'
    destination = output_root / "index.html"
else:
    root_prefix = "../" * depth
    aside = f'<aside><p class="index-label">Project notebook</p><nav><a href="{root_prefix}">README</a><a href="{root_prefix}docs/tutorial.html">Tutorial</a><a href="{root_prefix}docs/surface-syntax-reference.html">Syntax reference</a><a href="{root_prefix}docs/trust-model.html">Trust model</a></nav></aside>'
    destination = output_root / destination

page = f'''<!doctype html>
<html lang="en">
  <head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <meta name="description" content="Eponym brings dependent types and quantitative type checking to Nim as an embedded DSL.">
    <title>{escape(title)} · Eponym</title>
    <link rel="stylesheet" href="{root_prefix}site.css">
  </head>
  <body>
    <header class="topbar"><a href="{root_prefix}">Eponym / research notebook</a><span>Dependent types · Nim · QTT</span><a href="https://github.com/raven6941/eponym">GitHub ↗</a></header>
    <div class="layout" id="top">
      {aside}
      <main class="sheet"><div class="folio"><span>Field notes / language tools</span><span>{escape(source.as_posix())}</span></div><article id="readme">{content}</article><footer class="endnote"><a href="{root_prefix}">Project home</a> · <a href="https://github.com/raven6941/eponym">Source repository</a></footer></main>
    </div>
  </body>
</html>
'''
destination.parent.mkdir(parents=True, exist_ok=True)
destination.write_text(page)
