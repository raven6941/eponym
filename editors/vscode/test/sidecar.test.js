"use strict";

const assert = require("assert");
const { shedAtCursor } = require("../out/sidecar");

const source = [
  "shedsBlock:",
  "  proc branchDemo(n: Nat): Nat = add ( ![branchLeft] ) ( ![branchRight] )",
].join("\n");
const left = source.indexOf("![branchLeft]");
const right = source.indexOf("![branchRight]");

assert.strictEqual(shedAtCursor(source, left + 4)?.name, "branchLeft");
assert.strictEqual(shedAtCursor(source, right + 4)?.name, "branchRight");
assert.strictEqual(shedAtCursor(source, right + 16)?.name, "branchRight",
  "same-line fallback chooses the nearest shed marker");

console.log("--- sidecar cursor selection tests passed ---");
