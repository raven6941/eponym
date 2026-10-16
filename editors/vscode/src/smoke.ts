// Headless smoke test for the #136 VSCode extension pieces (no vscode
// API): drives the real compiled LSP server over stdio, fetches
// eponym/shedLayout for sheds_demo's shed, renders it, and asserts the
// webview HTML carries the hole and its goal.
//
// Usage (after `npm run build`):
//   LSP=../../src/eponym/lsp DEMO=../../examples/embedded/sheds_demo.nim node out/smoke.js
// The env defaults resolve from out/ up three levels to the repo root, so
// plain `npm run smoke` also works (the CI still passes them explicitly).

import { LspClient } from "./protocol";
import { boxToHtml, pageHtml } from "./render";
import { renderInlineShed } from "./inlineRender";
import {
  hasShedBlocks,
  eponymRepoRoot,
  sidecarCompileArgs,
  generateSidecar,
  shedBlocks,
  shedAtCursor,
  blockShedsAtCursor,
  sidecarPathFor,
  sidecarFresh,
  readSidecarShedNames,
} from "./sidecar";
import * as path from "path";
import * as fs from "fs";
import * as os from "os";

function check(cond: boolean, msg: string) {
  if (!cond) {
    console.error("SMOKE FAIL: " + msg);
    process.exit(1);
  }
  console.log("ok: " + msg);
}

async function main() {
  const lsp = process.env.LSP ?? path.resolve(__dirname, "..", "..", "..", "src", "eponym", "lsp");
  // Resolve: DEMO may be relative to the caller's cwd (as CI passes it),
  // while generateSidecar compiles with cwd=repoRoot.
  const demo = path.resolve(
    process.env.DEMO ?? path.resolve(__dirname, "..", "..", "..", "examples", "embedded", "sheds_demo.nim")
  );
  const uri = "file://" + demo;

  const client = new LspClient(lsp);
  await client.initialize(path.dirname(demo));
  check(true, "initialize ok");

  // Issue #153: sidecar generation -- the exact path the extension uses.
  check(hasShedBlocks(fs.readFileSync(demo, "utf8")),
    "hasShedBlocks detects shedsBlock in the demo");
  check(!hasShedBlocks("proc f(x: int): int = x + 1\n"),
    "hasShedBlocks rejects a shed-free file");
  const maybeRoot = eponymRepoRoot(path.dirname(demo));
  check(maybeRoot !== null && fs.existsSync(path.join(maybeRoot, "src", "eponym", "lsp.nim")),
    "eponymRepoRoot finds the repo root from the demo dir: " + maybeRoot);
  if (maybeRoot === null) throw new Error("repo root not found; cannot continue");
  const root: string = maybeRoot;
  check(eponymRepoRoot(path.parse(root).root) === null,
    "eponymRepoRoot returns null above the filesystem root's repo check");
  const cargs = sidecarCompileArgs(root, demo);
  check(cargs[0] === "c" && cargs.includes("--hints:off") &&
        cargs.includes("--path:" + path.join(root, "src")) &&
        cargs.includes("--path:" + path.join(root, "src", "eponym")) &&
        !cargs.some(a => a.includes("staging") || a.includes("relational")) &&
        cargs[cargs.length - 1] === demo,
    "sidecarCompileArgs builds the nim invocation: " + cargs.join(" "));
  // End-to-end: delete the sidecar and regenerate it via the real `nim c`,
  // exactly as the extension does on document open/save.
  const demoSidecar = demo.replace(/\.nim$/, ".sheds.json");
  fs.rmSync(demoSidecar, { force: true });
  const nimBin = process.env.NIMBIN ?? "nim";
  const gen = await generateSidecar(nimBin, root, demo);
  check(gen.ok, "generateSidecar compiles the demo (nim c): " + (gen.error ?? "ok"));
  check(fs.existsSync(demoSidecar),
    "generateSidecar wrote the sidecar: " + demoSidecar);
  const regen = JSON.parse(fs.readFileSync(demoSidecar, "utf8"));
  check(Array.isArray(regen.sheds) && regen.sheds.length === 1 &&
        regen.sheds[0].name === "quadBody",
    "regenerated sidecar carries the quadBody shed");

  const layout = await client.shedLayout(uri, "quadBody");
  check(!!layout && !!layout.box, "eponym/shedLayout returned a box tree");

  const html = boxToHtml(layout.box);
  check(html.includes("hole"), "rendered HTML marks the hole");
  check(html.includes("?0"), "rendered HTML shows hole ?0");
  check(html.includes("data-goal"), "rendered HTML carries the hole goal");

  const page = pageHtml(JSON.stringify(layout), "quadBody", ["quadBody"]);
  check(page.includes("acquireVsCodeApi"), "webview page wires vscode api");
  check(page.includes("refine"), "webview page has refine button");
  check(page.includes("case-split"), "webview page has case-split button");
  check(page.includes('id="shedpicker"') && page.includes("switchShed"),
    "webview page has the in-view shed picker posting switch-shed");
  check(page.includes('<option value="quadBody" selected>'),
    "shed picker lists the current shed selected");

  // Issue #190: cursor-aware shed detection over the source text.
  const demoText = fs.readFileSync(demo, "utf8");
  const blocks = shedBlocks(demoText);
  check(blocks.length === 1 && blocks[0].sheds.length === 1 &&
        blocks[0].sheds[0].name === "quadBody",
    "shedBlocks finds the one shedsBlock with its quadBody node");
  const nodeOff = demoText.indexOf("![ quadBody");
  check(nodeOff >= 0 && shedAtCursor(demoText, nodeOff + 4)?.name === "quadBody",
    "shedAtCursor: cursor inside the node resolves quadBody");
  const procLineOff = demoText.indexOf("proc quad");
  check(procLineOff >= 0 && shedAtCursor(demoText, procLineOff + 2)?.name === "quadBody",
    "shedAtCursor: cursor on the proc line (outside the node) resolves quadBody");
  check(shedAtCursor(demoText, 0) === null,
    "shedAtCursor: file top resolves nothing");
  const midBlock = blocks[0].start + 5;
  check(blockShedsAtCursor(demoText, midBlock).length === 1 &&
        blockShedsAtCursor(demoText, midBlock)[0].name === "quadBody",
    "blockShedsAtCursor: cursor in the block (outside the node) sees quadBody");
  check(blockShedsAtCursor(demoText, 0).length === 0,
    "blockShedsAtCursor: outside any block sees nothing");

  // The walkthrough demo (issue #192): one block, six shed nodes (the
  // #192 extension: give, case-split, and deep-nesting sheds on top of
  // the original three).
  const wt = path.resolve(path.dirname(demo), "sheds_walkthrough.nim");
  if (fs.existsSync(wt)) {
    // The walkthrough layout checks below need its sidecar; generate it
    // exactly as the extension does (a fresh checkout has none).
    const wtGen = await generateSidecar(nimBin, root, wt);
    check(wtGen.ok, "generateSidecar compiles the walkthrough (nim c): " + (wtGen.error ?? "ok"));
    const wtText = fs.readFileSync(wt, "utf8");
    const wtBlocks = shedBlocks(wtText);
    const wtNames = wtBlocks.flatMap((b) => b.sheds.map((s) => s.name));
    check(wtBlocks.length === 1 &&
          wtNames.join(",") === "quadBody,addThreeBody,shuffleBody,constABody,isZeroBody,constEndoBody",
      "shedBlocks finds all six walkthrough sheds: " + wtNames.join(","));
    const shuffleOff = wtText.indexOf("![shuffleBody");
    check(shuffleOff >= 0 && shedAtCursor(wtText, shuffleOff + 2)?.name === "shuffleBody",
      "shedAtCursor disambiguates the walkthrough's third shed");
    // A cursor in the block but outside any node sees all six (ambiguous).
    const inBody = wtBlocks[0].sheds[0].end + 2;
    check(blockShedsAtCursor(wtText, inBody).length === 6,
      "blockShedsAtCursor reports all six sheds when the block is ambiguous");

    // Issue #221: the inline view path against the real server — shedLayout
    // for each walkthrough shed, rendered by renderInlineShed exactly as the
    // expansion decoration would show it in the editor region.
    const wtUri = "file://" + wt;
    const keyHints = "r: refine  c: case-split  g: give  (Esc: collapse)";
    for (const name of wtNames) {
      const wl = await client.shedLayout(wtUri, name);
      check(!!wl && !!wl.box,
        `eponym/shedLayout returns a box tree for walkthrough shed ${name}`);
      // Deep-nesting sheds (constEndoBody) decompose the Pi goal into nested
      // binder boxes: the hole goal lives on the innermost box, not the top.
      const goals: string[] = [];
      const walk = (b: any): void => {
        if (b.holeGoal) goals.push(String(b.holeGoal));
        for (const p of b.premises ?? []) walk(p);
        if (b.conclusion) walk(b.conclusion);
        for (const c of b.children ?? []) walk(c);
      };
      walk(wl.box);
      check(goals.length > 0,
        `box tree for ${name} carries at least one hole goal`);
      const view = renderInlineShed(name, wl.box, { showButtons: true, keyHints });
      check(view.includes(name) && goals.some((g) => view.includes(g)),
        `inline view for ${name} shows the shed name and its goal`);
      check(view.includes("?") && view.includes(keyHints),
        `inline view for ${name} draws the hole box and the advisory keybinding line`);
      check(view.includes("[refine] [case-split] [give]"),
        `inline view for ${name} shows action buttons when enabled`);
      const viewNoBtn = renderInlineShed(name, wl.box, { showButtons: false, keyHints });
      check(!viewNoBtn.includes("[refine]") && viewNoBtn.includes(keyHints),
        `inline view for ${name}: buttons hideable via config, advisory line always shown`);
    }

    // Regression: renderers must not crash on partial boxes. Older server
    // binaries omit empty arrays (no top-level holeIds, etc.); boxToText/
    // boxToHtml used to throw "Cannot read properties of undefined". Strip
    // the array fields from a REAL shedLayout response and verify both
    // renderers survive it.
    const realBox = (await client.shedLayout(wtUri, "constABody")).box;
    const stripArrays = (b: any): any => {
      if (b === null || typeof b !== "object") return b;
      const out: any = {};
      for (const [k, v] of Object.entries(b)) {
        if (k === "holeIds" || k === "premises" || k === "children" || k === "header") {
          continue; // dropped entirely, like the old server
        } else if (v && typeof v === "object") {
          out[k] = stripArrays(v);
        } else {
          out[k] = v;
        }
      }
      return out;
    };
    const partialBox = stripArrays(JSON.parse(JSON.stringify(realBox)));
    check(!("holeIds" in partialBox),
      "regression fixture: stripped box really lacks holeIds");
    let partialView = "";
    try {
      partialView = renderInlineShed("constABody", partialBox, { showButtons: true, keyHints });
    } catch (e) {
      check(false, `renderInlineShed survives a partial box (threw: ${String(e)})`);
    }
    check(partialView.length > 0,
      "renderInlineShed renders non-empty text from a partial box");
    let partialHtml = "";
    try {
      partialHtml = boxToHtml(partialBox);
    } catch (e) {
      check(false, `boxToHtml survives a partial box (threw: ${String(e)})`);
    }
    check(partialHtml.includes("box"),
      "boxToHtml renders a partial box without throwing");
  }

  // Issue #190: sidecar freshness + name listing.
  check(sidecarPathFor(demo) === demoSidecar,
    "sidecarPathFor maps the demo to its sidecar path");
  check(sidecarFresh(demo), "sidecarFresh: regenerated sidecar is fresh");
  fs.utimesSync(demo, new Date(), new Date(Date.now() + 60_000));
  check(!sidecarFresh(demo), "sidecarFresh: source newer than sidecar is stale");
  fs.utimesSync(demo, new Date(), new Date(Date.now() - 60_000));
  check(sidecarFresh(demo), "sidecarFresh: sidecar newer than source is fresh again");
  check(JSON.stringify(readSidecarShedNames(demoSidecar)) === JSON.stringify(["quadBody"]),
    "readSidecarShedNames lists the sidecar sheds");
  check(readSidecarShedNames(path.join(os.tmpdir(), "no-such.sheds.json")).length === 0,
    "readSidecarShedNames on a missing sidecar yields []");

  // Unknown shed -> server error (not a hang).
  let err = "";
  try {
    await client.shedLayout(uri, "no-such-shed");
  } catch (e) {
    err = String(e);
  }
  check(err.includes("no layout"), "unknown shed yields an error, not a hang: " + err);

  // Issue #137: drive eponym/refineShed against the real server binary
  // with a fixture sidecar (macro-time state, as shedsBlock would write
  // it, including the recorded generated source).
  const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "shed-smoke-"));
  const nimFile = path.join(tmp, "demo.nim");
  fs.writeFileSync(nimFile, "-- fixture\n");
  const genSrc =
    "postulate Int : ?\n" +
    "proc doubleIt (n : Int) : Int = _\n" +
    "proc tripleIt (n : Int) : Int = _\n";
  const sidecar = {
    file: nimFile,
    errMsg: "",
    sheds: [
      { name: "shedA", draft: "", nimLine: 4, nimCol: 32, holeLine: 2,
        holeIdx: 0, holeCol: 33, genSrc, goal: "Int", ctx: ["n : Int"],
        status: "yellow" },
      { name: "shedB", draft: "", nimLine: 5, nimCol: 32, holeLine: 3,
        holeIdx: 1, holeCol: 33, genSrc, goal: "Int", ctx: ["n : Int"],
        status: "yellow" },
    ],
  };
  const sidecarPath = path.join(tmp, "demo.sheds.json");
  fs.writeFileSync(sidecarPath, JSON.stringify(sidecar));
  const uri2 = "file://" + nimFile;

  const names = await client.shedNames(uri2);
  check(Array.isArray(names) && names.length === 2 && names[0] === "shedA",
    "eponym/shedNames lists the fixture sheds: " + JSON.stringify(names));

  const r1 = await client.refineShed(uri2, "shedA", "addInt n n");
  check(r1.status === "white" && r1.term === "addInt n n" &&
        r1.nimLine === 4 && r1.nimCol === 32 && r1.yellowCount === 1,
    "eponym/refineShed fills the hole server-side: " + JSON.stringify(r1));

  const sidecar2 = JSON.parse(fs.readFileSync(sidecarPath, "utf8"));
  check(sidecar2.sheds[0].status === "white" &&
        sidecar2.sheds[0].genSrc.includes("addInt n n"),
    "sidecar rewritten: shedA white with the filled source");
  check(sidecar2.sheds[1].status === "yellow" &&
        sidecar2.sheds[1].holeLine === 3,
    "sidecar rewritten: shedB still yellow on line 3");

  let err2 = "";
  try {
    await client.refineShed(uri2, "no-such-shed", "n");
  } catch (e) {
    err2 = String(e);
  }
  check(err2.includes("unknown shed"),
    "refineShed on an unknown shed yields an error: " + err2);

  fs.rmSync(tmp, { recursive: true, force: true });

  // Issue #208: the webview case-split path (textDocument/codeAction with
  // `variable`) needs the document opened first. Before didOpen the server
  // answers "unknown document"; after didOpen the codeAction path reaches
  // case-split; didChange refreshes the buffer the server reasons about.
  const epLines = [
    "data Nat : ? where",
    "| zero : Nat",
    "| suc (n : Nat) : Nat",
    "def add : Nat -> Nat -> Nat",
    "| zero n = n",
    "| (suc m) n = suc (add m n)",
    "data Vec (A : ?) : Nat -> ? where",
    "| nil : Vec A zero",
    "| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)",
    "proc append {A : ?} {m : Nat} {n : Nat} (xs : Vec A m) (ys : Vec A n) : Vec A (add m n) =",
    "  _",
    "",
  ];
  const epSrc1 = epLines.join("\n");
  // Same text with the explicit arguments swapped: ys is now the first
  // explicit argument, so case-split applies to it instead of xs.
  const epSrc2 = epSrc1.replace(
    "proc append {A : ?} {m : Nat} {n : Nat} (xs : Vec A m) (ys : Vec A n) : Vec A (add m n) =",
    "proc append {A : ?} {m : Nat} {n : Nat} (ys : Vec A n) (xs : Vec A m) : Vec A (add n m) ="
  );
  const epUri = "file:///tmp/shed-smoke-case-split.ep";
  const holePos = { line: 10, character: 2 }; // 0-based: the `  _` line
  const caseSplitReq = (variable: string) => ({
    textDocument: { uri: epUri },
    range: { start: holePos, end: holePos },
    context: { diagnostics: [] },
    variable,
  });
  let preOpenErr = "";
  try {
    await client.request("textDocument/codeAction", caseSplitReq("xs"));
  } catch (e) {
    preOpenErr = String(e);
  }
  check(preOpenErr.includes("unknown document"),
    "codeAction before didOpen fails as 'unknown document': " + preOpenErr);
  client.didOpen(epUri, epSrc1);
  const cs1 = await client.request("textDocument/codeAction", caseSplitReq("xs"));
  check(Array.isArray(cs1) && cs1.some((a: any) => a.title === "case-split xs"),
    "codeAction after didOpen offers 'case-split xs': " +
      JSON.stringify(cs1 && cs1.map((a: any) => a.title)));
  let ysFirstErr = "";
  try {
    await client.request("textDocument/codeAction", caseSplitReq("ys"));
  } catch (e) {
    ysFirstErr = String(e);
  }
  check(ysFirstErr.includes("first explicit argument"),
    "case-split on the second argument is rejected, as designed: " + ysFirstErr);
  // didChange swaps the buffer: the server must now split on ys, not xs.
  client.didChange(epUri, epSrc2);
  const cs2 = await client.request("textDocument/codeAction", caseSplitReq("ys"));
  check(Array.isArray(cs2) && cs2.some((a: any) => a.title === "case-split ys"),
    "codeAction after didChange offers 'case-split ys': " +
      JSON.stringify(cs2 && cs2.map((a: any) => a.title)));
  let xsNowErr = "";
  try {
    await client.request("textDocument/codeAction", caseSplitReq("xs"));
  } catch (e) {
    xsNowErr = String(e);
  }
  check(xsNowErr.includes("first explicit argument"),
    "xs is now the second argument and is rejected: " + xsNowErr);

  client.shutdown();
  console.log("--- shed webview smoke passed ---");
}

main().catch((e) => {
  console.error("SMOKE FAIL: " + String(e));
  process.exit(1);
});
