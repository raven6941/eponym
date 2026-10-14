# shed_layout.nim -- 2D box layout engine (issue #135), Epigram deduction style.
#
# Given a shed's proof state (or a core term with holes), compute a 2D box
# tree mimicking the deduction layouts in the Epigram papers (McBride 2005
# AFP notes; Altenkirch-McBride-McKinna 2005): premises (sub-deductions)
# sit side-by-side *above* a horizontal rule, the conclusion sits *below*
# it, optionally labeled. The layout rules from the issue:
#
# - Case/eliminator: branches laid out left-to-right as side-by-side boxes
#   (`caseBox`).
# - Let-sequence: vertically stacked boxes (`letSeq`: each binding is a
#   deduction with the bound value above the rule, the rest below).
# - Induction: header ("by induction on n") with case boxes below
#   (`inductionBox`).
# - Holes: empty boxes showing the goal type (`holeBox`), carrying their
#   hole IDs for click-to-refine wiring (issue #136).
# - Each box: content lines, measured width/height, child boxes, hole IDs.
#
# Core terms render as natural-deduction trees: application (Pi-elim) puts
# the function and argument side-by-side above the rule; pair-intro puts
# the components above the rule; let is a labeled deduction. Metavariables
# (`tMeta`, i.e. holes) render as hole boxes with their goal type.
#
# Two outputs: `renderBox` (ASCII/Unicode art, for tests and the demo) and
# `boxToJson` (the shape the LSP method `eponym/shedLayout` returns, for
# the #136 webview).

import json
import strutils
import unicode  # runeLen: display width of header text
import eponym_init  # Term, TermKind (`$` for Term)
import sheds  # ShedInfo (layoutShed)

type
  BoxArrange* = enum
    baVertical    ## children stacked (let-sequences, lambda bodies)
    baHorizontal  ## children side by side (case/eliminator branches)

  Box* = ref object
    ## One 2D box. Two shapes:
    ## - *rule* (premises non-empty): premises side-by-side above a
    ##   horizontal rule (labeled by `ruleLabel`, "" = unlabeled); below
    ##   the rule sits `conclusion` (nil = `header` is the conclusion).
    ## - *plain* (premises empty): `header` lines, then `children`
    ##   arranged per `arrange`.
    header*: seq[string]
    premises*: seq[Box]
    ruleLabel*: string
    conclusion*: Box
    children*: seq[Box]
    arrange*: BoxArrange
    holeIds*: seq[int]  ## hole IDs under this box (for click-to-refine)
    holeGoal*: string   ## hole boxes show their goal; "" = not a hole box
    width*, height*: int  ## measured outer size, borders included

const gap = 2  ## columns between side-by-side boxes

proc dwidth(s: string): int = s.runeLen

proc center(s: string, w: int): string =
  ## Center `s` in a field of width `w` (display columns).
  let pad = max(0, w - dwidth(s))
  let left = pad div 2
  ' '.repeat(left) & s & ' '.repeat(pad - left)

proc maxHeaderW(b: Box): int =
  result = 0
  for h in b.header: result = max(result, dwidth(h))

# --- constructors -------------------------------------------------------

proc textBox*(lines: varargs[string]): Box =
  ## Plain content box (context lines, atom terms, messages).
  Box(header: @lines, arrange: baVertical)

proc holeBox*(holeId: int, goal: string): Box =
  ## An empty box showing the goal type at a hole (issue #135).
  Box(header: @["?" & $holeId & " : " & goal],
      holeIds: @[holeId], holeGoal: goal, arrange: baVertical)

proc ruleBox*(premises: seq[Box], ruleLabel: string,
              conclusion: Box): Box =
  ## A deduction: premises above the rule, `conclusion` below it.
  doAssert premises.len > 0, "ruleBox needs at least one premise"
  doAssert conclusion != nil, "ruleBox needs a conclusion"
  Box(premises: premises, ruleLabel: ruleLabel, conclusion: conclusion,
      arrange: baHorizontal)

proc goalStateBox*(ctx: seq[string], holeId: int, goal: string,
                   goalPi: seq[string] = @[]): Box =
  ## A shed's proof state, Epigram-style: the context hypotheses (stacked)
  ## above the rule, the hole (empty box showing its goal) below it.
  ## Issue #192: when `goalPi` is non-empty -- the goal's Pi spine as
  ## strings, binders outermost-first, residual goal last -- one box nests
  ## per binder around the hole box, so a shed over a function type with
  ## multiple binders shows real nesting instead of one flat hole box.
  var inner = holeBox(holeId, if goalPi.len > 0: goalPi[^1] else: goal)
  for i in countdown(goalPi.len - 2, 0):
    inner = Box(header: @[goalPi[i]], children: @[inner],
                arrange: baVertical)
  ruleBox(@[textBox(ctx)], "", inner)

proc caseBox*(scrutinee: string,
              branches: seq[tuple[pat: string, body: Box]]): Box =
  ## Case/eliminator: one header, branches as side-by-side boxes.
  var bs: seq[Box] = @[]
  for (pat, body) in branches:
    bs.add(Box(header: @[pat], children: @[body], arrange: baVertical))
  Box(header: @["case " & scrutinee], children: bs,
      arrange: baHorizontal)

proc inductionBox*(varName: string,
                   cases: seq[tuple[pat: string, body: Box]]): Box =
  ## Induction: header "by induction on n" with case boxes below.
  let inner = caseBox(varName, cases)
  Box(header: @["by induction on " & varName], children: inner.children,
      arrange: baHorizontal)

proc letSeq*(binds: seq[tuple[name, ty: string, val: Box]],
             body: Box): Box =
  ## Let-sequence: vertically stacked deductions, each binding a labeled
  ## rule (value above, the rest of the sequence below).
  result = body
  for i in countdown(binds.high, 0):
    let (name, ty, val) = binds[i]
    result = ruleBox(@[val], "let " & name & " : " & ty, result)

proc layoutShed*(shed: ShedInfo): Box =
  ## The box tree `eponym/shedLayout` returns for a shed: its proof state
  ## (context above the rule, hole below). A shed with no open hole
  ## (white) gets a plain "done" box instead.
  if shed.holeIdx >= 0:
    goalStateBox(shed.ctx, shed.holeIdx, shed.goal, shed.goalPi)
  else:
    textBox("shed '" & shed.name & "' elaborated: no open holes")

# --- term layout: core terms as deduction trees ---------------------------

proc layoutTerm*(t: Term, holeGoalOf: proc(id: int): string): Box =
  ## Render a core term as a natural-deduction box tree. Holes (`tMeta`)
  ## become hole boxes; eliminations put their sub-deductions side-by-side
  ## above the rule. `holeGoalOf` supplies the goal type for a hole id.
  case t.kind
  of tMeta:
    holeBox(t.metaId, holeGoalOf(t.metaId))
  of tApp:  # Pi-elim: function and argument above the rule
    ruleBox(@[layoutTerm(t.fn, holeGoalOf), layoutTerm(t.arg, holeGoalOf)],
            "", textBox($t))
  of tPair:  # Si-intro: components above the rule
    ruleBox(@[layoutTerm(t.pFst, holeGoalOf), layoutTerm(t.pSnd, holeGoalOf)],
            "", textBox($t))
  of tFst, tSnd, tAbsurd:  # Si-elim / absurdity: premise above the rule
    ruleBox(@[layoutTerm(t.sub, holeGoalOf)], "", textBox($t))
  of tLet:  # the bound value above a labeled rule, body below
    ruleBox(@[layoutTerm(t.letVal, holeGoalOf)],
            "let " & t.letScope.adv & " : " & $t.letTy,
            layoutTerm(t.letScope.bdy, holeGoalOf))
  of tLam:  # binder line, body stacked below
    Box(header: @["lam " & t.scope.adv & " : " & $t.dom],
        children: @[layoutTerm(t.scope.bdy, holeGoalOf)],
        arrange: baVertical)
  else:  # tR, tV, tPi, tSi, tC, tInt, tNatLit, tPrim: atoms
    textBox($t)

# --- measuring ------------------------------------------------------------

proc measure*(b: Box) =
  ## Bottom-up: set `width`/`height` (outer, borders included).
  if b.premises.len > 0:
    var pw = 0
    var ph = 0
    for p in b.premises:
      measure(p)
      pw += p.width + gap
      ph = max(ph, p.height)
    pw -= gap
    let labelW = if b.ruleLabel == "": 0 else: dwidth(b.ruleLabel) + 2
    measure(b.conclusion)
    let inner = max([pw, b.conclusion.width, maxHeaderW(b), labelW])
    b.width = inner + 2
    b.height = 1 + ph + 1 + b.conclusion.height + 1
  elif b.children.len > 0:
    var cw = 0
    var ch = 0
    for c in b.children:
      measure(c)
      if b.arrange == baVertical:
        cw = max(cw, c.width)
        ch += c.height
      else:
        cw += c.width + gap
        ch = max(ch, c.height)
    if b.arrange == baHorizontal and b.children.len > 0:
      cw -= gap
    let inner = max(cw, maxHeaderW(b))
    b.width = inner + 2
    b.height = 1 + b.header.len + ch + 1
  else:
    b.width = maxHeaderW(b) + 2
    b.height = b.header.len + 2

# --- ASCII rendering ------------------------------------------------------

proc renderLines(b: Box): seq[string] =
  ## Render to lines, borders included. `measure` must have run.
  let inner = b.width - 2
  result = @["\u250C" & "\u2500".repeat(inner) & "\u2510"]  # ┌─┐
  if b.premises.len > 0:
    # Premises side-by-side above the rule.
    var pr: seq[seq[string]] = @[]
    var ph = 0
    for p in b.premises:
      let lines = renderLines(p)
      pr.add(lines)
      ph = max(ph, lines.len)
    for i in 0 ..< pr.len:
      while pr[i].len < ph:
        pr[i].add(' '.repeat(b.premises[i].width))
    for r in 0 ..< ph:
      var row = ""
      for i in 0 ..< pr.len:
        if i > 0: row &= ' '.repeat(gap)
        row &= pr[i][r]
      result.add("\u2502" & center(row, inner) & "\u2502")  # │ │
    # The rule, labeled or plain.
    if b.ruleLabel == "":
      result.add("\u251C" & "\u2500".repeat(inner) & "\u2524")  # ├─┤
    else:
      let rest = inner - 2 - dwidth(b.ruleLabel)
      result.add("\u251C\u2500" & b.ruleLabel & " " &
                 "\u2500".repeat(max(0, rest)) & "\u2524")
    # Conclusion below the rule (header lines when conclusion is nil are
    # handled by treating them as the conclusion box -- ruleBox always
    # has a conclusion, so this branch is just defensive).
    if b.conclusion != nil:
      for l in renderLines(b.conclusion):
        result.add("\u2502" & center(l, inner) & "\u2502")
    else:
      for h in b.header:
        result.add("\u2502" & center(h, inner) & "\u2502")
  else:
    for h in b.header:
      result.add("\u2502" & center(h, inner) & "\u2502")
    if b.children.len > 0:
      if b.arrange == baVertical:
        for c in b.children:
          for l in renderLines(c):
            result.add("\u2502" & center(l, inner) & "\u2502")
      else:
        var cr: seq[seq[string]] = @[]
        var ch = 0
        for c in b.children:
          let lines = renderLines(c)
          cr.add(lines)
          ch = max(ch, lines.len)
        for i in 0 ..< cr.len:
          while cr[i].len < ch:
            cr[i].add(' '.repeat(b.children[i].width))
        for r in 0 ..< ch:
          var row = ""
          for i in 0 ..< cr.len:
            if i > 0: row &= ' '.repeat(gap)
            row &= cr[i][r]
          result.add("\u2502" & center(row, inner) & "\u2502")
  result.add("\u2514" & "\u2500".repeat(inner) & "\u2518")  # └─┘

proc renderBox*(b: Box): string =
  ## The 2D ASCII/Unicode rendering of the box tree.
  measure(b)
  renderLines(b).join("\n")

# --- hole wiring + JSON (for the #136 webview) -----------------------------

proc allHoleIds*(b: Box): seq[int] =
  ## Every hole ID under this box, premises/conclusion/children included.
  result = b.holeIds
  for p in b.premises: result.add(allHoleIds(p))
  if b.conclusion != nil: result.add(allHoleIds(b.conclusion))
  for c in b.children: result.add(allHoleIds(c))

proc boxToJson*(b: Box): JsonNode =
  ## The box tree as JSON for `eponym/shedLayout`.
  measure(b)
  var premises = newJArray()
  for p in b.premises: premises.add(boxToJson(p))
  var children = newJArray()
  for c in b.children: children.add(boxToJson(c))
  %*{"header": b.header,
      "ruleLabel": b.ruleLabel,
      "premises": premises,
      "conclusion": (if b.conclusion == nil: newJNull()
                     else: boxToJson(b.conclusion)),
      "children": children,
      "arrange": $b.arrange,
      "holeIds": allHoleIds(b),
      "holeGoal": b.holeGoal,
      "width": b.width, "height": b.height}

when isMainModule:
  # Smoke: goal-state layout of a shed with one hole.
  let b = goalStateBox(@["n : Int"], 0, "Int")
  echo renderBox(b)
  doAssert allHoleIds(b) == @[0]
  doAssert boxToJson(b)["holeIds"] == % @[0]
