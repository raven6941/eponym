// End-to-end check for a Nimble-library user's workspace, outside the repo.
import * as fs from "fs";
import * as path from "path";
import { pathToFileURL } from "url";
import { LspClient } from "./protocol";
import { boxToHtml } from "./render";
import { generateSidecarForSource, hasShedBlocks, sidecarFresh } from "./sidecar";
import { buildServerBinary, discoverEponymSource } from "./serverSetup";

function check(condition: boolean, message: string): void {
  if (!condition) throw new Error(`Nimble extension smoke failed: ${message}`);
  console.log(`ok: ${message}`);
}

async function main(): Promise<void> {
  const project = process.env.EPONYM_NIMBLE_PROJECT;
  const storage = process.env.EPONYM_NIMBLE_STORAGE;
  if (!project || !storage) throw new Error("EPONYM_NIMBLE_PROJECT and EPONYM_NIMBLE_STORAGE are required");
  const file = path.join(project, "sheds_user.nim");
  const sourceText = fs.readFileSync(file, "utf8");
  check(hasShedBlocks(sourceText), "detects a shed block in the external project");

  const source = await discoverEponymSource(project);
  check(source !== null && source.kind === "nimble", "discovers the Nimble package with no checkout");
  if (!source || source.kind !== "nimble") throw new Error("Nimble package source was not found");

  const generated = await generateSidecarForSource(process.env.NIMBIN ?? "nim", source, file);
  check(generated.ok, `compiles the user's file against the installed package: ${generated.error ?? "ok"}`);
  check(sidecarFresh(file), "writes a fresh sidecar next to the project file");

  const server = await buildServerBinary(process.env.NIMBIN ?? "nim", source, storage, project);
  const client = new LspClient(server);
  try {
    await client.initialize(project);
    const uri = pathToFileURL(file).toString();
    const names = await client.shedNames(uri);
    check(names.includes("installedBody"), "installed-source LSP reads the generated sidecar");
    const layout = await client.shedLayout(uri, "installedBody");
    const box = layout?.box;
    check(!!box, "installed-source LSP returns a shed layout");
    if (!box) throw new Error("shed layout is empty");
    check(boxToHtml(box).includes("hole"), "rendered layout contains the open hole");
  } finally {
    client.shutdown();
  }
}

main().catch((error) => {
  console.error(error);
  process.exitCode = 1;
});
