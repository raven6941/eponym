// Test suite entry point, executed INSIDE the VS Code extension host by
// @vscode/test-electron. Must export `run`. Runs each scenario file in
// test/integration/suite/scenarios sequentially and reports a summary.
//
// No mocha dependency: scenarios are plain async `run()` functions so the
// suite has zero extra test-framework machinery to maintain.
const path = require("path");
const fs = require("fs");

async function run() {
  const scenariosDir = path.join(__dirname, "scenarios");
  const files = fs.readdirSync(scenariosDir).filter((f) => f.endsWith(".js")).sort();
  if (files.length === 0) throw new Error("no integration scenarios found");
  let failed = 0;
  for (const f of files) {
    const mod = require(path.join(scenariosDir, f));
    try {
      await mod.run();
      console.log(`[integration] PASS ${f}`);
    } catch (e) {
      failed++;
      console.error(`[integration] FAIL ${f}: ${e && e.stack ? e.stack : e}`);
    }
  }
  if (failed > 0) throw new Error(`${failed}/${files.length} integration scenario(s) failed`);
  console.log(`[integration] all ${files.length} scenarios passed`);
}

module.exports = { run };
