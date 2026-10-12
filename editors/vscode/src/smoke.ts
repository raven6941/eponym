// Headless smoke test for the #136 VSCode extension pieces (no vscode
// API): drives the real compiled LSP server over stdio, fetches
// eponym/shedLayout for sheds_demo's shed, renders it, and asserts the
// webview HTML carries the hole and its goal.
//
// Usage (after `npm run build`):
//   LSP=../../src/eponym/lsp DEMO=../../examples/embedded/sheds_demo.nim node out/smoke.js

import { LspClient } from "./protocol";
import { boxToHtml, pageHtml } from "./render";
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
  const lsp = process.env.LSP ?? path.resolve(__dirname, "..", "..", "src", "eponym", "lsp");
  const demo = process.env.DEMO ?? path.resolve(__dirname, "..", "..", "examples", "embedded", "sheds_demo.nim");
  const uri = "file://" + demo;

  const client = new LspClient(lsp);
  await client.initialize(path.dirname(demo));
  check(true, "initialize ok");

  const layout = await client.shedLayout(uri, "quadBody");
  check(!!layout && !!layout.box, "eponym/shedLayout returned a box tree");

  const html = boxToHtml(layout.box);
  check(html.includes("hole"), "rendered HTML marks the hole");
  check(html.includes("?0"), "rendered HTML shows hole ?0");
  check(html.includes("data-goal"), "rendered HTML carries the hole goal");

  const page = pageHtml(JSON.stringify(layout), "quadBody");
  check(page.includes("acquireVsCodeApi"), "webview page wires vscode api");
  check(page.includes("refine"), "webview page has refine button");
  check(page.includes("case-split"), "webview page has case-split button");

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

  client.shutdown();
  console.log("--- shed webview smoke passed ---");
}

main().catch((e) => {
  console.error("SMOKE FAIL: " + String(e));
  process.exit(1);
});
